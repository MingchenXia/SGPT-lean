import SGPT.Foundations.Schemes.FiniteGradedPolynomialAugmentedVanishing
import SGPT.Foundations.Schemes.HomogeneousScalarKernelQuotient

/-!
# Eventual saturation of a graded quotient of a polynomial ring

This file extracts from `SGPT.Foundations.Schemes`'s Čech theory of finite graded modules over a
polynomial ring over a field (Serre's theorem on `ℙᴺ_K`: the degree-`k` piece of a finite graded
`K[X₀, …, X_N]`-module agrees with its degree-`k` coordinate Čech cocycles for `k ≫ 0`) the
elementary statement used for the finite generation of the filtration of an ample test
configuration (lane FG-REL, [BHJ17, Prop. 2.15]):

*Let `J ⊆ K[X₀, …, X_N]` be a homogeneous ideal. There is `b` such that for every `k ≥ b`, every
`D` and every family `p_i ∈ K[X]_{k+D}` with `X_j^D p_i ≡ X_i^D p_j (mod J)` there is
`c ∈ K[X]_k` with `X_i^E (X_i^D c - p_i) ∈ J` for some `E` and every `i`.*

In the language of sheaves: the compatible family `p_i / X_i^D` is a section of `𝒪_Z(k)`,
`Z = V(J) ⊆ ℙᴺ`, and for `k ≫ 0` it comes from the degree-`k` piece of `K[X]/J`.

## Main results

* `cechCocycleOfFamily`: a compatible family of fractions `m_i / x_i^D` as a Čech cocycle of
  `SGPT.Foundations.Schemes.homogeneousCoordinateSubsetDiagram`.
* `degreeToCocycles_val_singleton`: the value of the degree map on a singleton.
* `exists_saturation_lift`: the statement above (`K` a field, `J` homogeneous).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.FGRel

open CategoryTheory SGPT.Foundations.Schemes

universe u

/-! ### Compatible families of fractions as Čech cocycles -/

section Cocycle

variable {K R M I : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M] [LinearOrder I]
  (𝒜 : ℤ → Submodule K R) [GradedRing 𝒜]
  (ℳ : ℤ → Submodule K M) [SetLike.GradedSMul 𝒜 ℳ]
  (x : I → R) (hx : ∀ i, x i ∈ 𝒜 1)

omit [LinearOrder I] in
theorem card_pos_of_card_eq_one {S : Finset I} (h : S.card = 1) : S.Nonempty :=
  Finset.card_pos.mp (by omega)

/-- The underlying fraction of an element of the coordinate diagram. -/
def dval {k : ℤ} {S : Finset I} (z : (homogeneousCoordinateSubsetDiagram 𝒜 ℳ x hx k).obj S) :
    LocalizedModule (Submonoid.powers (homogeneousCoordinateSubsetProduct x S)) M :=
  Subtype.val (show localizedHomogeneousModulePiece 𝒜 ℳ (homogeneousCoordinateSubsetProduct x S)
    (S.card : ℤ) (homogeneousCoordinateSubsetProduct_degree 𝒜 x hx S) k from z)

/-- The value on `S` of the Čech cochain `(m_i / x_i^D)_i` (zero unless `S` is a singleton). -/
def cochainValue (k : ℤ) (D : ℕ) (m : I → M) (hm : ∀ i, m i ∈ ℳ (k + D)) (S : Finset I) :
    (homogeneousCoordinateSubsetDiagram 𝒜 ℳ x hx k).obj S :=
  if h : S.card = 1 then
    (⟨LocalizedModule.mk (m (S.min' (card_pos_of_card_eq_one h)))
        (homogeneousPowerDenominator (homogeneousCoordinateSubsetProduct x S) D),
      ⟨D, m (S.min' (card_pos_of_card_eq_one h)), by
        rw [h]
        simpa using hm (S.min' (card_pos_of_card_eq_one h)), rfl⟩⟩ :
      localizedHomogeneousModulePiece 𝒜 ℳ (homogeneousCoordinateSubsetProduct x S)
        (S.card : ℤ) (homogeneousCoordinateSubsetProduct_degree 𝒜 x hx S) k)
  else 0

theorem cochainValue_val_singleton (k : ℤ) (D : ℕ) (m : I → M) (hm : ∀ i, m i ∈ ℳ (k + D))
    (i : I) :
    dval 𝒜 ℳ x hx (cochainValue 𝒜 ℳ x hx k D m hm {i}) =
      LocalizedModule.mk (m i)
        (homogeneousPowerDenominator (homogeneousCoordinateSubsetProduct x {i}) D) := by
  unfold cochainValue dval
  rw [dif_pos (Finset.card_singleton i)]
  simp only [Finset.min'_singleton]

/-- The restriction maps of the coordinate diagram on literal fractions. -/
theorem diagram_map_val {k : ℤ} {S T : Finset I} (hST : S ⊆ T) (c : R)
    (hc : homogeneousCoordinateSubsetProduct x T = homogeneousCoordinateSubsetProduct x S * c)
    (z : (homogeneousCoordinateSubsetDiagram 𝒜 ℳ x hx k).obj S) (n : ℕ) (m : M)
    (hz : dval 𝒜 ℳ x hx z =
      LocalizedModule.mk m (homogeneousPowerDenominator (homogeneousCoordinateSubsetProduct x S) n)) :
    dval 𝒜 ℳ x hx (subsetCechRestriction (homogeneousCoordinateSubsetDiagram 𝒜 ℳ x hx k) hST z) =
      LocalizedModule.mk (c ^ n • m)
        (homogeneousPowerDenominator (homogeneousCoordinateSubsetProduct x T) n) := by
  change actualLocalizedModuleDivisorRestriction (M := M)
    (homogeneousCoordinateSubsetProduct x S) (homogeneousCoordinateSubsetProduct x T)
      (homogeneousCoordinateSubsetProduct_dvd x hST) (dval 𝒜 ℳ x hx z) = _
  rw [hz]
  exact actualLocalizedModuleDivisorRestriction_mk _ _ c hc m n

/-- **A compatible family of fractions is a Čech cocycle**: if `m_i ∈ ℳ_{k+D}` and
`x_j^D m_i = x_i^D m_j` for all `i, j`, then `(m_i / x_i^D)_i` is a degree-`k` cocycle. -/
def cechCocycleOfFamily (k : ℤ) (D : ℕ) (m : I → M) (hm : ∀ i, m i ∈ ℳ (k + D))
    (hcomp : ∀ i j, x j ^ D • m i = x i ^ D • m j) :
    LinearMap.ker
      (subsetCechCardDifferential (homogeneousCoordinateSubsetDiagram 𝒜 ℳ x hx k) 1) := by
  classical
  refine ⟨⟨cochainValue 𝒜 ℳ x hx k D m hm, fun S hS => ?_⟩, ?_⟩
  · unfold cochainValue
    rw [dif_neg hS]
  · rw [LinearMap.mem_ker]
    apply Subtype.ext
    funext S
    change subsetCechDifferential _ (cochainValue 𝒜 ℳ x hx k D m hm) S = 0
    by_cases hS : S.card = 2
    · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hS
      wlog hlt : i < j generalizing i j
      · have hji : j < i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hij)
        have := this j i (Ne.symm hij) (by rw [Finset.pair_comm]; exact hS) hji
        rwa [Finset.pair_comm] at this
      rw [subsetCechDifferential_apply, Finset.sum_pair hij]
      have hsi : subsetCechSign ({i, j} : Finset I) i = 1 := by
        unfold subsetCechSign
        have : ({i, j} : Finset I).filter (fun l => l < i) = ∅ := by
          ext l
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
            Finset.notMem_empty, iff_false, not_and]
          rintro (rfl | rfl) h
          · exact lt_irrefl _ h
          · exact lt_asymm h hlt
        rw [this, Finset.card_empty, pow_zero]
      have hsj : subsetCechSign ({i, j} : Finset I) j = -1 := by
        unfold subsetCechSign
        have : ({i, j} : Finset I).filter (fun l => l < j) = {i} := by
          ext l
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl, h⟩
            · rfl
            · exact absurd h (lt_irrefl _)
          · rintro rfl
            exact ⟨Or.inl rfl, hlt⟩
        rw [this, Finset.card_singleton, pow_one]
      rw [hsi, hsj, one_smul, neg_smul, one_smul, ← sub_eq_add_neg, sub_eq_zero]
      have hei : ({i, j} : Finset I).erase i = {j} := by
        rw [Finset.erase_insert (by simpa using hij)]
      have hej : ({i, j} : Finset I).erase j = {i} := by
        ext l
        simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨h1, rfl | rfl⟩
          · rfl
          · exact absurd rfl h1
        · rintro rfl
          exact ⟨hij, Or.inl rfl⟩
      apply Subtype.ext
      have hpi : homogeneousCoordinateSubsetProduct x ({i, j} : Finset I) =
          homogeneousCoordinateSubsetProduct x (({i, j} : Finset I).erase i) * x i := by
        rw [hei]
        simp [homogeneousCoordinateSubsetProduct, Finset.prod_pair hij, mul_comm]
      have hpj : homogeneousCoordinateSubsetProduct x ({i, j} : Finset I) =
          homogeneousCoordinateSubsetProduct x (({i, j} : Finset I).erase j) * x j := by
        rw [hej]
        simp [homogeneousCoordinateSubsetProduct, Finset.prod_pair hij]
      have vi : ∀ (S : Finset I) (hS1 : S.card = 1),
          dval 𝒜 ℳ x hx (cochainValue 𝒜 ℳ x hx k D m hm S) =
            LocalizedModule.mk (m (S.min' (card_pos_of_card_eq_one hS1)))
              (homogeneousPowerDenominator (homogeneousCoordinateSubsetProduct x S) D) := by
        intro S hS1
        unfold cochainValue dval
        rw [dif_pos hS1]
      have h1 := diagram_map_val 𝒜 ℳ x hx (Finset.erase_subset i {i, j}) (x i) hpi
        (cochainValue 𝒜 ℳ x hx k D m hm (({i, j} : Finset I).erase i)) D _
        (vi _ (by rw [hei, Finset.card_singleton]))
      have h2 := diagram_map_val 𝒜 ℳ x hx (Finset.erase_subset j {i, j}) (x j) hpj
        (cochainValue 𝒜 ℳ x hx k D m hm (({i, j} : Finset I).erase j)) D _
        (vi _ (by rw [hej, Finset.card_singleton]))
      change dval 𝒜 ℳ x hx _ = dval 𝒜 ℳ x hx _
      rw [h1, h2]
      have emi : (({i, j} : Finset I).erase i).min'
          (card_pos_of_card_eq_one (by rw [hei, Finset.card_singleton])) = j := by
        simp only [hei, Finset.min'_singleton]
      have emj : (({i, j} : Finset I).erase j).min'
          (card_pos_of_card_eq_one (by rw [hej, Finset.card_singleton])) = i := by
        simp only [hej, Finset.min'_singleton]
      rw [emi, emj, hcomp j i]
    · exact subsetCechDifferential_mem_cardPiece _ 1
        ⟨cochainValue 𝒜 ℳ x hx k D m hm, fun S hS => by
          unfold cochainValue
          rw [dif_neg hS]⟩ S hS

/-- The degree map to cocycles, evaluated on a singleton: the fraction `v / 1`. -/
theorem degreeToCocycles_val_singleton (k : ℤ) (v : ℳ k) (i : I) :
    dval 𝒜 ℳ x hx (((homogeneousCoordinateDegreeToCocycles 𝒜 ℳ x hx k v :
        subsetCechCardPiece (homogeneousCoordinateSubsetDiagram 𝒜 ℳ x hx k) 1) :
          subsetCechCube (homogeneousCoordinateSubsetDiagram 𝒜 ℳ x hx k)) {i}) =
      LocalizedModule.mk (v : M) 1 := by
  change dval 𝒜 ℳ x hx (subsetCechDifferential _ _ {i}) = _
  rw [subsetCechDifferential_apply, Finset.sum_singleton]
  have hs : subsetCechSign ({i} : Finset I) i = 1 := by
    unfold subsetCechSign
    have : ({i} : Finset I).filter (fun l => l < i) = ∅ := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false,
        not_and]
      rintro rfl
      exact lt_irrefl _
    rw [this, Finset.card_empty, pow_zero]
  rw [hs, one_smul]
  have he : ({i} : Finset I).erase i = ∅ := Finset.erase_singleton i
  have hsub : (∅ : Finset I) ⊆ {i} := Finset.empty_subset _
  rw [subsetCechRestriction_value_congr _ _ (Finset.erase_subset i {i}) hsub he]
  have h0 : ((subsetCechCardPiece (homogeneousCoordinateSubsetDiagram 𝒜 ℳ x hx k) 0).subtype
      (homogeneousCoordinateDegreeToCardZero 𝒜 ℳ x hx k v)) ∅ =
      homogeneousCoordinateEmptyPieceMap 𝒜 ℳ x hx k v := by
    simp [homogeneousCoordinateDegreeToCardZero, subsetCechCardZeroEquiv]
  rw [h0]
  change actualLocalizedModuleDivisorRestriction (M := M)
    (homogeneousCoordinateSubsetProduct x ∅) (homogeneousCoordinateSubsetProduct x {i})
      (homogeneousCoordinateSubsetProduct_dvd x hsub)
      (LocalizedModule.mkLinearMap (Submonoid.powers (homogeneousCoordinateSubsetProduct x ∅)) M
        (v : M)) = _
  rw [← LinearMap.comp_apply, actualLocalizedModuleDivisorRestriction_comp]
  rfl

end Cocycle

/-! ### Eventual saturation over a field -/

section Field

variable {K I : Type u} [Field K] [LinearOrder I] [Fintype I] [Nonempty I]

/-- The quotient grading of `K[X]/J` for a homogeneous ideal `J`. -/
abbrev quotientGrading (J : Submodule (MvPolynomial I K) (MvPolynomial I K)) :
    ℤ → Submodule K (MvPolynomial I K ⧸ J) :=
  homogeneousRingQuotientPiece (polynomialIntegralGrading (K := K) (I := I)) J

set_option backward.isDefEq.respectTransparency true in
/-- **Serre's theorem in elementary form** (`K` a field, `J` a homogeneous ideal of
`K[X_i]`): there is `b` such that for `k ≥ b`, every compatible family `p_i / X_i^D` of
degree `k` (`p_i ∈ K[X]_{k+D}`, `X_j^D p_i ≡ X_i^D p_j mod J`) comes, modulo `J` and powers of
`X_i`, from one `c ∈ K[X]_k`. -/
theorem exists_saturation_lift (J : Submodule (MvPolynomial I K) (MvPolynomial I K))
    (hJ : J.IsHomogeneous (polynomialIntegralGrading (K := K) (I := I))) :
    ∃ b : ℤ, ∀ k : ℤ, b ≤ k → ∀ (D : ℕ) (p : I → MvPolynomial I K),
      (∀ i, p i ∈ polynomialIntegralGrading (K := K) (I := I) (k + D)) →
      (∀ i j, MvPolynomial.X j ^ D * p i - MvPolynomial.X i ^ D * p j ∈ J) →
      ∃ c ∈ polynomialIntegralGrading (K := K) (I := I) k, ∀ i, ∃ E : ℕ,
        MvPolynomial.X i ^ E * (MvPolynomial.X i ^ D * c - p i) ∈ J := by
  classical
  let ℳ := quotientGrading J
  let dec : DirectSum.Decomposition ℳ :=
    homogeneousRingQuotientDecomposition (polynomialIntegralGrading (K := K) (I := I)) J hJ
  have gs : SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := I)) ℳ :=
    homogeneousRingQuotientGradedSMul (polynomialIntegralGrading (K := K) (I := I)) J
      (polynomialIntegralGrading (K := K) (I := I))
  have fin : Module.Finite (MvPolynomial I K) (MvPolynomial I K ⧸ J) :=
    inferInstance
  obtain ⟨b, hb⟩ :=
    finiteGradedPolynomialCoordinateDegreeToCocycles_eventually_bijective (K := K) (I := I)
      (M := MvPolynomial I K ⧸ J) ℳ
  refine ⟨b, fun k hk D p hp hcomp => ?_⟩
  let m : I → MvPolynomial I K ⧸ J := fun i => J.mkQ (p i)
  have hm : ∀ i, m i ∈ ℳ (k + D) := fun i => Submodule.mem_map.mpr ⟨p i, hp i, rfl⟩
  have hmcomp : ∀ i j, (MvPolynomial.X j : MvPolynomial I K) ^ D • m i =
      (MvPolynomial.X i : MvPolynomial I K) ^ D • m j := by
    intro i j
    simp only [m]
    rw [← LinearMap.map_smul, ← LinearMap.map_smul, ← sub_eq_zero, ← map_sub,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul, smul_eq_mul]
    exact hcomp i j
  obtain ⟨v, hv⟩ := (hb k hk).2
    (cechCocycleOfFamily (polynomialIntegralGrading (K := K) (I := I)) ℳ
      (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree k D m hm hmcomp)
  obtain ⟨c, hc, hcv⟩ := Submodule.mem_map.mp v.property
  refine ⟨c, hc, fun i => ?_⟩
  have h1 := degreeToCocycles_val_singleton (polynomialIntegralGrading (K := K) (I := I)) ℳ
    (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree k v i
  rw [hv] at h1
  have h2 := cochainValue_val_singleton (polynomialIntegralGrading (K := K) (I := I)) ℳ
    (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree k D m hm i
  have h3 := h1.symm.trans h2
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp h3
  obtain ⟨E, hE⟩ := u.property
  have hprod : homogeneousCoordinateSubsetProduct (fun i => (MvPolynomial.X i : MvPolynomial I K))
      {i} = MvPolynomial.X i := by
    simp [homogeneousCoordinateSubsetProduct]
  refine ⟨E, ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
  simp only [Submonoid.smul_def, homogeneousPowerDenominator, one_smul] at hu
  rw [← hE, hprod] at hu
  rw [mul_sub, map_sub, sub_eq_zero, ← smul_eq_mul, ← smul_eq_mul, map_smul, map_smul,
    ← smul_eq_mul (MvPolynomial.X i ^ E) (p i), map_smul]
  rw [show J.mkQ c = (v : MvPolynomial I K ⧸ J) from hcv]
  exact hu

end Field

end SGPT.TestCurve.FGRel

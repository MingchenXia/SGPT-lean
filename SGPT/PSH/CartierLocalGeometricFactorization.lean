import SGPT.PSH.CartierPrimeGermMultiplicity

set_option autoImplicit false
noncomputable section


namespace SGPT.PSH

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open InvertibleIdealQuotient RegularLocusComponent AnalyticGermDecomposition
open scoped Topology Manifold ContDiff

private theorem squarefree_emultiplicity {A : Type*} [CommMonoidWithZero A]
    [IsCancelMulZero A] {q r : A} (hq : Prime q) (hr : Squarefree r) [Decidable (q ∣ r)] :
    emultiplicity q r = if q ∣ r then 1 else 0 := by
  classical
  by_cases hdiv : q ∣ r
  · rw [if_pos hdiv]
    apply le_antisymm
    · exact ((squarefree_iff_emultiplicity_le_one r).mp hr q).resolve_right hq.not_isUnit
    · simpa only [ENat.natCast_one] using (pow_dvd_iff_le_emultiplicity (a := q) (b := r) (k := 1)).mp (by simpa only [pow_one] using hdiv)
  · rw [if_neg hdiv]
    exact emultiplicity_eq_zero.mpr hdiv

private theorem associated_grouped_product {A : Type*} [CommMonoidWithZero A]
    [UniqueFactorizationMonoid A] [Nontrivial A]
    {ι : Type*} [Fintype ι] (D : A) (hD : D ≠ 0) (R : ι → A)
    (hR : ∀ j, R j ≠ 0) (hs : ∀ j, Squarefree (R j)) (a : ι → ℕ)
    (hsupport : ∀ q, Prime q → (q ∣ D ↔ ∃ j, q ∣ R j))
    (hdisjoint : ∀ q, Prime q → ∀ i j, q ∣ R i → q ∣ R j → i = j)
    (hmult : ∀ q, Prime q → ∀ j, q ∣ R j → multiplicity q D = a j) :
    Associated D (∏ j, R j ^ a j) := by
  classical
  have hprod : (∏ j, R j ^ a j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (hR j))
  have heq (q : A) (hq : Prime q) :
      emultiplicity q D = emultiplicity q (∏ j, R j ^ a j) := by
    rw [Finset.emultiplicity_prod hq]
    by_cases hqd : q ∣ D
    · obtain ⟨j, hj⟩ := (hsupport q hq).mp hqd
      have hterms (i : ι) : emultiplicity q (R i ^ a i) =
          if i = j then (a j : ENat) else 0 := by
        rw [emultiplicity_pow hq, squarefree_emultiplicity hq (hs i)]
        by_cases hij : i = j
        · subst i
          simp only [if_pos hj, mul_one, ite_true]
        · have hi : ¬q ∣ R i := fun hi => hij (hdisjoint q hq i j hi hj)
          simp only [if_neg hi, mul_zero, if_neg hij]
      simp_rw [hterms]
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ j),
        (FiniteMultiplicity.of_prime_left hq hD).emultiplicity_eq_multiplicity, hmult q hq j hj]
    · have hnot (i : ι) : ¬q ∣ R i := fun hi => hqd ((hsupport q hq).mpr ⟨i, hi⟩)
      rw [emultiplicity_eq_zero.mpr hqd]
      apply Eq.symm
      apply Finset.sum_eq_zero
      intro i _
      rw [emultiplicity_pow hq, emultiplicity_eq_zero.mpr (hnot i), mul_zero]
  exact associated_of_dvd_dvd
    ((UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hD).mpr (fun q hq => le_of_eq (heq q hq)))
    ((UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hprod).mpr
      (fun q hq => le_of_eq (heq q hq).symm))

universe u
variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem exists_mk_finset_prod {ι : Type*} (s : Finset ι)
    (f : ι → ComplexModel (m + 1) → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f i) z) :
    ∃ hP : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun x => ∏ i ∈ s, f i x) z,
      HolGerm.mk (fun x => ∏ i ∈ s, f i x) hP = ∏ i ∈ s, HolGerm.mk (f i) (hf i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty] using
      (⟨eventually_differentiableAt_one, HolGerm.mk_one⟩ :
        ∃ hP : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
            DifferentiableAt ℂ (fun _ => (1 : ℂ)) z,
          HolGerm.mk (fun _ => (1 : ℂ)) hP = 1)
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    obtain ⟨hP, hPC⟩ := ih
    refine ⟨eventually_differentiableAt_mul (hf i) hP, ?_⟩
    rw [HolGerm.mk_mul (f i) (fun x => ∏ j ∈ s, f j x) (hf i) hP, hPC]

/-- The original divisor and point ALONE produce the literal weighted
singular prime product, with the SAME actual geometric coefficients, exact
reduced chart-germ ideals, nearby ORIGINAL ideal generator and actual unit. -/
theorem exists_cartier_local_geometric_factorization (D : EffectiveDivisor (m + 1) M) (x : M) :
    ∃ (g : M → ℂ)
      (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ
        (fun z => g ((complexChartAt (n := m + 1) x).val.symm
          (z + (complexChartAt (n := m + 1) x).val x))) z),
      HolGerm.mk (fun z => g ((complexChartAt (n := m + 1) x).val.symm
        (z + (complexChartAt (n := m + 1) x).val x))) hf ≠ 0 ∧
      (∀ᶠ y in 𝓝 x, HolomorphicAt (m + 1) g y ∧ ∀ b,
        D.ideal.mem y b ↔ IsInSpanAt (n := m + 1) (· = g) y b) ∧
      AnalyticDescendingChain.chartGerm (n := m + 1) D.support x =ᶠ[𝓝 0]
        {z | g ((complexChartAt (n := m + 1) x).val.symm
          (z + (complexChartAt (n := m + 1) x).val x)) = 0} ∧
      ∃ S : Finset (GlobalComponents.globalComponents (n := m + 1) D.support),
        ∃ (r : GlobalComponents.globalComponents (n := m + 1) D.support →
            ComplexModel (m + 1) → ℂ)
          (hr : ∀ B, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (r B) z),
          (∀ B, HolGerm.mk (r B) (hr B) ≠ 0 ∧ Squarefree (HolGerm.mk (r B) (hr B)) ∧
            vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1)
              (cartierPrimeComponent D B).carrier x) = Ideal.span {HolGerm.mk (r B) (hr B)} ∧
            AnalyticDescendingChain.chartGerm (n := m + 1)
              (cartierPrimeComponent D B).carrier x =ᶠ[𝓝 0] {z | r B z = 0}) ∧
          (∀ B ∈ S, 0 < regularComponentOrder D D.support B) ∧
          (∃ T ∈ 𝓝 x, ∀ y ∈ T, y ∈ D.support ↔
            ∃ B ∈ S, y ∈ (cartierPrimeComponent D B).carrier) ∧
          ∃ (U : ComplexModel (m + 1) → ℂ)
            (_hU : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ U z),
            U 0 ≠ 0 ∧ (∀ᶠ z in 𝓝 0, U z ≠ 0) ∧
            (fun z => g ((complexChartAt (n := m + 1) x).val.symm
              (z + (complexChartAt (n := m + 1) x).val x))) =ᶠ[𝓝 0]
                fun z => (∏ B : {B // B ∈ S}, r B.val z ^
                  regularComponentOrder D D.support B.val) * U z := by
  classical
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel (m + 1))) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean (m + 1)
  obtain ⟨g, hf, hF, hgen, hzero, T, hxT, S, hcover, r, hr, hRdata, hsupport, hdisjoint⟩ :=
    exists_cartier_local_prime_equations D x
  let f : ComplexModel (m + 1) → ℂ := fun z =>
    g ((complexChartAt (n := m + 1) x).val.symm (z + (complexChartAt (n := m + 1) x).val x))
  let I := {B // B ∈ S}
  let R : I → HolGerm (ComplexModel (m + 1)) := fun B => HolGerm.mk (r B.val) (hr B.val)
  let a : I → ℕ := fun B => regularComponentOrder D D.support B.val
  have hsupport' (Q : HolGerm (ComplexModel (m + 1))) (hQ : Prime Q) :
      Q ∣ HolGerm.mk f hf ↔ ∃ B : I, Q ∣ R B := by
    rw [hsupport Q hQ]
    exact ⟨fun ⟨B, hBS, hQB⟩ => ⟨⟨B, hBS⟩, hQB⟩, fun ⟨B, hQB⟩ => ⟨B.val, B.property, hQB⟩⟩
  have hdisjoint' (Q : HolGerm (ComplexModel (m + 1))) (hQ : Prime Q)
      (B C : I) (hQB : Q ∣ R B) (hQC : Q ∣ R C) : B = C :=
    Subtype.ext (hdisjoint Q hQ B.val C.val hQB hQC)
  have hmult (Q : HolGerm (ComplexModel (m + 1))) (hQ : Prime Q)
      (B : I) (hQB : Q ∣ R B) : multiplicity Q (HolGerm.mk f hf) = a B := by
    obtain ⟨q, hq, rfl⟩ := HolGerm.exists_eq_mk Q
    have hmem : HolGerm.mk (r B.val) (hr B.val) ∈ vanishingIdeal {z | q z = 0} := by
      rw [(ActualPrimeGermGenericAvoidance.vanishingIdeal_zeroSet_eq_and_irreducible q hq hQ).1]
      exact Ideal.mem_span_singleton.mpr hQB
    have hvan : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), q z = 0 → r B.val z = 0 :=
      mem_vanishingIdeal_mk.mp hmem
    have hbranch : {z | q z = 0} ≤ᶠ[𝓝 0]
        AnalyticDescendingChain.chartGerm (n := m + 1) (cartierPrimeComponent D B.val).carrier x := by
      filter_upwards [hvan, Filter.eventuallyEq_set.mp (hRdata B.val).2.2.2] with z hz heq hzQ
      exact heq.mpr (hz hzQ)
    exact (regularComponentOrder_eq_primeGerm_multiplicity D x g hf hF hgen hzero
      q hq hQ B.val hbranch).symm
  have hassoc := associated_grouped_product (HolGerm.mk f hf) hF R
    (fun B => (hRdata B.val).1) (fun B => (hRdata B.val).2.1) a hsupport' hdisjoint' hmult
  obtain ⟨unit, heq⟩ := hassoc.symm
  obtain ⟨U, hU, hUrep⟩ := HolGerm.exists_eq_mk (unit : HolGerm (ComplexModel (m + 1)))
  have hU0 : U 0 ≠ 0 := by
    have hv := (HolGerm.isUnit_iff_eval_ne_zero _).mp unit.isUnit
    rwa [hUrep, HolGerm.eval_mk] at hv
  obtain ⟨hP, hPC⟩ := exists_mk_finset_prod Finset.univ
    (fun B : I => fun z => r B.val z ^ a B)
    (fun B => eventually_differentiableAt_pow (hr B.val) (a B))
  have hprodEq : HolGerm.mk (fun z => ∏ B : I, r B.val z ^ a B) hP = ∏ B : I, R B ^ a B := by
    rw [hPC]
    exact Finset.prod_congr rfl fun B _ => HolGerm.mk_pow (r B.val) (hr B.val) (a B)
  have hfuneq : HolGerm.mk f hf = HolGerm.mk
      (fun z => (∏ B : I, r B.val z ^ a B) * U z) (eventually_differentiableAt_mul hP hU) := by
    rw [HolGerm.mk_mul (fun z => ∏ B : I, r B.val z ^ a B) U hP hU, hprodEq, ← hUrep]
    exact heq.symm
  exact ⟨g, hf, hF, hgen, hzero, S, r, hr, hRdata,
    (fun B _ => regularComponentOrder_pos D B), ⟨T, hxT, hcover⟩,
    U, hU, hU0, hU.self_of_nhds.continuousAt.eventually_ne hU0, HolGerm.mk_eq_mk_iff.mp hfuneq⟩

end SGPT.PSH

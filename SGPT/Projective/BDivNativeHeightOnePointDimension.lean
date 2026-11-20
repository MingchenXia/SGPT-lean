import SGPT.Projective.BDivNativePointDimensionResidue
import SGPT.Foundations.Schemes.FiniteTypeDomainClosedPointDimension
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! For a height-one prime, isolate its component of a principal divisor
on a nonempty basic affine open and use the principal ideal height bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.BDivNov16

open AlgebraicGeometry CategoryTheory Set TopologicalSpace
open scoped BigOperators nonZeroDivisors
open SGPT.Foundations.Schemes SGPT.Projective.NumEq.AlgebraicCurveDegree

/-- A nonempty basic open of an integral finite-type affine scheme has the same dimension. -/
private theorem ringKrullDim_away_of_nonzero (k A : Type) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (s : A) (hs : s ≠ 0) :
    ringKrullDim (Localization.Away s) = ringKrullDim A := by
  let B := Localization.Away s
  let : IsDomain B := IsLocalization.Away.isDomain B hs
  let L := FractionRing A
  have hu : IsUnit (algebraMap A L s) := by
    apply isUnit_iff_ne_zero.mpr
    simpa only [map_zero] using (IsFractionRing.injective A L).ne hs
  let h : B →+* L := IsLocalization.Away.lift s hu
  let : Algebra B L := h.toAlgebra
  let : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.Away.lift_comp (S := B) s hu).symm
  let : IsScalarTower k B L := IsScalarTower.of_algebraMap_eq fun a => calc
    algebraMap k L a = algebraMap A L (algebraMap k A a) :=
      IsScalarTower.algebraMap_apply k A L a
    _ = algebraMap B L (algebraMap A B (algebraMap k A a)) :=
      IsScalarTower.algebraMap_apply A B L _
    _ = algebraMap B L (algebraMap k B a) := by
      rw [IsScalarTower.algebraMap_apply k A B a]
  let : IsFractionRing B L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers s) B L
  obtain ⟨n, hA, htrA⟩ := actualFiniteTypeFractionDimension k A L
  obtain ⟨m, hB, htrB⟩ := actualFiniteTypeFractionDimension k B L
  have he : n = m := by exact_mod_cast htrA.symm.trans htrB
  rw [hA, hB, he]

/-- Localization of an affine closed subset cannot increase its dimension. -/
private theorem ringKrullDim_away_quotient_le (A : Type) [CommRing A] (s : A)
    (P : Ideal A) :
    ringKrullDim (Localization.Away s ⧸ P.map (algebraMap A (Localization.Away s))) ≤
      ringKrullDim (A ⧸ P) := by
  let B := Localization.Away s
  let e := IsLocalization.primeSpectrumOrderIso (Submonoid.powers s) B
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  refine Order.krullDim_le_of_strictMono (fun z => ⟨(e z.val).val, ?_⟩) ?_
  · change P ≤ Ideal.comap (algebraMap A B) z.val.asIdeal
    exact Ideal.map_le_iff_le_comap.mp z.property
  · intro x y hxy
    exact e.lt_iff_lt.mpr hxy

/-- A height-one prime containing a nonzero element is minimal over the ideal of that element. -/
private theorem heightOne_mem_minimalPrimes_span {A : Type} [CommRing A] [IsDomain A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1) {r : A} (hr : r ∈ P) (hr0 : r ≠ 0) :
    P ∈ (Ideal.span {r}).minimalPrimes := by
  refine ⟨⟨inferInstance, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hr)⟩, ?_⟩
  intro Q hQ hQP
  let : Q.IsPrime := hQ.1
  by_contra hPQ
  have hlt : Q < P := lt_of_le_not_ge hQP hPQ
  have hbound := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [hP] at hbound
  have hcancel : 1 + Q.height ≤ (1 : ℕ∞) + 0 := calc
    _ = Q.height + 1 := add_comm _ _
    _ ≤ 1 := hbound
    _ = _ := (add_zero _).symm
  have hQ0 : Q.height = 0 :=
    le_antisymm ((ENat.add_le_add_iff_left (by simp : (1 : ℕ∞) ≠ ⊤)).mp hcancel) bot_le
  have he : Q = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp hQ0
  have hrQ : r ∈ Q := hQ.2 (Ideal.subset_span (Set.mem_singleton r))
  exact hr0 (by simpa [he] using hrQ)

/-- Invert one product to remove every other minimal component of the principal divisor. -/
private theorem exists_away_radical_span_eq {A : Type} [CommRing A] [IsNoetherianRing A]
    (P : Ideal A) [P.IsPrime] {r : A} (hP : P ∈ (Ideal.span {r}).minimalPrimes) :
    ∃ s : A, s ∉ P ∧
      (Ideal.span ({algebraMap A (Localization.Away s) r} :
        Set (Localization.Away s))).radical = P.map (algebraMap A (Localization.Away s)) := by
  classical
  let I : Ideal A := Ideal.span {r}
  let E := {Q : Ideal A // Q ∈ I.minimalPrimes ∧ Q ≠ P}
  let : Fintype E := ((Ideal.finite_minimalPrimes_of_isNoetherianRing A I).subset
    (show {Q : Ideal A | Q ∈ I.minimalPrimes ∧ Q ≠ P} ⊆ I.minimalPrimes from
      fun _ h => h.1)).fintype
  have chooseFactor (Q : E) : ∃ a : A, a ∈ Q.val ∧ a ∉ P := by
    by_contra h
    have hQP : Q.val ≤ P := by
      intro x hx
      by_contra hxp
      exact h ⟨x, hx, hxp⟩
    exact Q.property.2 (le_antisymm hQP (hP.2 Q.property.1.1 hQP))
  choose a ha hna using chooseFactor
  let s : A := ∏ Q : E, a Q
  have hs : s ∉ P := by
    intro h
    obtain ⟨Q, _, hQ⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hna Q hQ
  have hsQ (Q : E) : s ∈ Q.val := by
    obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ Q)
    change s = a Q * b at hb
    rw [hb]
    exact Q.val.mul_mem_right b (ha Q)
  refine ⟨s, hs, ?_⟩
  let B := Localization.Away s
  let S := Submonoid.powers s
  let J : Ideal B := Ideal.span {algebraMap A B r}
  let P' : Ideal B := P.map (algebraMap A B)
  have hJ : I.map (algebraMap A B) = J := by simp [I, J, Ideal.map_span]
  have hPdis : Disjoint (S : Set A) (P : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime (I := P) s).mpr hs
  have hP'under : P'.under A = P :=
    IsLocalization.under_map_of_isPrime_disjoint S B inferInstance hPdis
  have hminimal : J.minimalPrimes = {P'} := by
    ext Q
    constructor
    · intro hQ
      have hdis := ((IsLocalization.isPrime_iff_isPrime_disjoint S B Q).mp hQ.isPrime).2
      have hQunder : Q.under A ∈ I.minimalPrimes := by
        rwa [← hJ, IsLocalization.minimalPrimes_map S] at hQ
      have he : Q.under A = P := by
        by_contra hne
        exact Set.disjoint_left.mp hdis (Submonoid.mem_powers s)
          (hsQ ⟨Q.under A, hQunder, hne⟩)
      rw [Set.mem_singleton_iff, ← IsLocalization.map_under S B Q, he]
    · intro hQ
      rw [Set.mem_singleton_iff] at hQ
      rw [hQ, ← hJ, IsLocalization.minimalPrimes_map S]
      change P'.under A ∈ I.minimalPrimes
      rwa [hP'under]
  change J.radical = P'
  rw [← Ideal.sInf_minimalPrimes, hminimal, sInf_singleton]

/-- A height-one prime in an integral affine algebra of finite type over a
field has quotient dimension one below the dimension of the original ring. -/
theorem finiteTypeDomain_quotient_dim_add_one_of_height_one
    (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1) :
    ringKrullDim (A ⧸ P) + 1 = ringKrullDim A := by
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨r, hr, hrnot⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr
    (Ideal.ne_bot_of_height_eq_one hP))
  have hr0 : r ≠ 0 := by simpa using hrnot
  have hupper := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk P)
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hr0)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  obtain ⟨s, hs, hrad⟩ := exists_away_radical_span_eq P
    (heightOne_mem_minimalPrimes_span P hP hr hr0)
  have hs0 : s ≠ 0 := fun he => hs (by simp [he])
  let B := Localization.Away s
  let : IsDomain B := IsLocalization.Away.isDomain B hs0
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  let J : Ideal B := Ideal.span {algebraMap A B r}
  let P' : Ideal B := P.map (algebraMap A B)
  have hP'dis : Disjoint (Submonoid.powers s : Set A) (P : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime (I := P) s).mpr hs
  let : P'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) B P inferInstance hP'dis
  have hle : J ≤ P' :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_map_of_mem _ hr))
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P' Ideal.IsPrime.ne_top'
  let : M.IsMaximal := hM
  have hrM : algebraMap A B r ∈ M :=
    hPM (hle (Ideal.subset_span (Set.mem_singleton _)))
  have hdim : ringKrullDim B ≤ ringKrullDim (B ⧸ J) + 1 := by
    rw [← finiteTypeDomain_maximalIdeal_height_eq_dimension k B M]
    exact Ideal.height_le_ringKrullDim_quotient_add_one hrM
  have hquot : ringKrullDim (B ⧸ J) = ringKrullDim (B ⧸ P') := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient, ← PrimeSpectrum.zeroLocus_radical J, hrad]
  have hlocal : ringKrullDim B = ringKrullDim A := ringKrullDim_away_of_nonzero k A s hs0
  refine le_antisymm hupper ?_
  rw [← hlocal]
  refine hdim.trans ?_
  rw [hquot]
  simpa only [add_comm] using add_le_add_right (ringKrullDim_away_quotient_le A s P) 1

/-- The original point closure of a codimension-one point on an integral scheme
locally of finite type over a field has dimension one below the scheme. -/
theorem nativePointDimension_add_one_eq_topologicalKrullDim_of_coheight_one
    {k : Type} [Field k] {V : Scheme.{0}} [IsIntegral V] (f : V ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (v : V) (hv : Order.coheight v = 1) :
    (↑(pointDimension V v + 1) : WithBot ℕ∞) = topologicalKrullDim V := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hvU, -⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open (show v ∈ (⊤ : V.Opens) from trivial)
      (⊤ : V.Opens).isOpen
  let : Nonempty U := ⟨⟨v, hvU⟩⟩
  let A := Γ(V, U)
  let := nativeAffineChartAlgebra f U
  let : Algebra.FiniteType k A := nativeAffineChartAlgebra_finiteType f hU
  let q : Spec (.of A) := hU.primeIdealOf ⟨v, hvU⟩
  have hq : q.asIdeal.height = 1 := by
    rw [idealHeight_eq_coheight]
    calc
      Order.coheight q = Order.coheight (hU.fromSpec q) :=
        (coheight_eq_of_isOpenImmersion hU.fromSpec).symm
      _ = Order.coheight v :=
        congrArg (fun y : V => Order.coheight y) (hU.fromSpec_primeIdealOf ⟨v, hvU⟩)
      _ = 1 := hv
  have hpoint := nativePointDimension_eq_affine_quotient f v hU hvU
  calc
    _ = (↑(pointDimension V v) : WithBot ℕ∞) + 1 := by
      rw [WithBot.coe_add, WithBot.coe_one]
    _ = ringKrullDim (A ⧸ q.asIdeal) + 1 := by rw [hpoint]
    _ = ringKrullDim A := finiteTypeDomain_quotient_dim_add_one_of_height_one k A q.asIdeal hq
    _ = topologicalKrullDim V := (nativeTopologicalKrullDim_eq_affine f hU).symm

end SGPT.Projective.BDivNov16

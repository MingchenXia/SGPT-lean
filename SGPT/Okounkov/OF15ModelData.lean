import SGPT.Okounkov.OF13LogResolution

/-!
# Algebraic coordinates at the centre of a valuation on an algebraized log resolution

Source: chapter *The theory of Okounkov bodies*, `rmk:valcurr` (presentations `ν = ν_{Y•} g` by
smooth flags) via `rmk:Abhyankar` (existence part of [CFKLRS17, Thm 2.9]).

Lane OF13 (`OF13.exists_admissibleFlag_lexEquivalent_of_analyticLogResolution`) proves that a
valuation `ν` with `ν(u_k) = e_k`, centred at a complex point `p` of an integral smooth projective
model `V` at which the `u_k` form an analytic log resolution, is equivalent to an admissible flag
valuation; its statement keeps only the flag. Lane OF15 needs the data produced on the way, to
build a **smooth** flag out of the analytic members and compare. This file re-runs the argument and
exposes:

* **`exists_coordinates_of_analyticLogResolution`**: every coordinate index is a member
  (`M = univ`, rank argument); algebraic local equations `z₁, …, zₙ ∈ 𝒪_{V,x}` of the members whose
  analytic germs are units times the analytic coordinates `ℓⱼ` (Chow); the `z` are strict normal
  crossings coordinates; and an order `σ` of the coordinates for which the matrix
  `(ν(z_{σ(i)}))ᵢ` is unit upper triangular (the monomial cone).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.OF15

open CategoryTheory AlgebraicGeometry Filter Set IsLocalRing SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.Okounkov.OF5 SGPT.Okounkov.OF6 SGPT.Okounkov.ValCurr
open SGPT.Okounkov.OF13
open scoped Topology Manifold

section Scheme

variable {V : Scheme.{0}} {g : V ⟶ Spec (.of ℂ)} {n : ℕ}
  [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g]

local instance of15mdTopology : TopologicalSpace (SchemeComplexPoint g) :=
  schemeAnalyticPointTopology g
local instance of15mdCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g n
local instance of15mdManifold : IsComplexManifold n (SchemeComplexPoint g) :=
  schemeAnalyticTN_isComplexManifold g n

/-- **Algebraic coordinates at the centre.** Under the hypotheses of lane OF13's
`exists_admissibleFlag_lexEquivalent_of_analyticLogResolution` (`ν` centred at the image `x` of
the complex point `p`; holomorphic coordinates `ℓ` at `p`; members `Hⱼ = {ℓⱼ = 0}`, `j ∈ M`;
`u_k = η_k ∏_{j ∈ M} ℓⱼ^{a_{kj}}` as meromorphic germs with `ν(u_k) = e_k`), every index is a
member, and there are `z₁, …, zₙ ∈ 𝒪_{V,x}` with analytic germs `Bⱼ ℓⱼ` (`Bⱼ` units) forming strict
normal crossings coordinates and a permutation `σ` such that `(ν(z_{σ(i)}))ᵢ` is unit upper
triangular. -/
theorem exists_coordinates_of_analyticLogResolution {X : Scheme.{0}}
    [IsIntegral X] [IsIntegral V] (EV : ClosedProjectiveEmbedding g)
    (e : X.functionField ≃+* V.functionField)
    (ν : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (p : SchemeComplexPoint g)
    (hcent : AlgebraicValuation.IsValuationCenter (ν.comap e.symm.toRingHom)
      (schemeComplexPointImage g p))
    (ℓ : Fin n → SchemeComplexPoint g → ℂ) (hℓ : ∀ j, HolomorphicAt n (ℓ j) p)
    (hcoord : Ideal.span (Set.range fun j =>
        NativeHolGerm.chartEquiv p (NativeHolGerm.mk (ℓ j) (hℓ j))) =
      maximalIdeal (HolGerm (ComplexModel n)))
    (M : Finset (Fin n)) (H : Fin n → Set (SchemeComplexPoint g))
    (hH : ∀ j ∈ M, IsComplexAnalyticSubset (n := n) (H j))
    (hℓmem : ∀ j ∈ M, (vanishingIdeal (n := n) (H j)).mem p (ℓ j))
    (hℓgen : ∀ j ∈ M, ∀ (h : SchemeComplexPoint g → ℂ) (hh : HolomorphicAt n h p),
      (vanishingIdeal (n := n) (H j)).mem p h →
        NativeHolGerm.mk h hh ∈ Ideal.span {NativeHolGerm.mk (ℓ j) (hℓ j)})
    (u : Fin n → X.functionField) (η : Fin n → (NativeHolGerm n (SchemeComplexPoint g) p)ˣ)
    (a : Fin n → Fin n → ℤ) (haM : ∀ k, ∀ j ∉ M, a k j = 0)
    (hu : ∀ k, schemeNativeFunctionFieldGerm g n p (e (u k)) =
      algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint g) p))
          (η k : NativeHolGerm n (SchemeComplexPoint g) p) *
        ∏ j, (algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint g) p))
          (NativeHolGerm.mk (ℓ j) (hℓ j))) ^ (a k j))
    (hreg : ∀ k, (∃ h : NativeHolGerm n (SchemeComplexPoint g) p,
        schemeNativeFunctionFieldGerm g n p (e (u k)) =
          algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint g) p)) h) ∨
      ∃ h : NativeHolGerm n (SchemeComplexPoint g) p,
        schemeNativeFunctionFieldGerm g n p (e (u k))⁻¹ =
          algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint g) p)) h)
    (hνu : ∀ k, ν (u k) = basisValue k) :
    M = Finset.univ ∧
    ∃ (z : Fin n → V.presheaf.stalk (schemeComplexPointImage g p))
      (B : Fin n → (NativeHolGerm n (SchemeComplexPoint g) p)ˣ) (σ : Equiv.Perm (Fin n)),
      (∀ j, schemeNativeStalkGerm g n p (z j) = B j * NativeHolGerm.mk (ℓ j) (hℓ j)) ∧
      OF11.IsSNCCoordinates g (schemeComplexPointImage g p) z ∧
      IsUnitUpperTriangular (fun i => ofLex (((ν.comap e.symm.toRingHom)
        (algebraMap _ V.functionField (z (σ i)))).untopD 0)) := by
  classical
  let G := NativeHolGerm n (SchemeComplexPoint g) p
  let L := FractionRing G
  let O := V.presheaf.stalk (schemeComplexPointImage g p)
  let w : Fin n → G := fun j => NativeHolGerm.mk (ℓ j) (hℓ j)
  let ν' := ν.comap e.symm.toRingHom
  obtain ⟨v, hv⟩ := dualVectors_of_span_eq _ hcoord
  have hw0 : ∀ j, w j ≠ 0 := fun j h => by
    have h1 := hv j j
    change germDeriv (v j) (NativeHolGerm.chartEquiv p (w j)) = _ at h1
    rw [h, map_zero, germDeriv_zero, if_pos rfl] at h1
    exact zero_ne_one h1
  have hinj := schemeNativeStalkGerm_injective g n p
  have hff := schemeNativeStalkGerm_faithfullyFlat g n p
  have hΓ := schemeNativeFunctionFieldGerm_eq_fractionMap g n p
  have hBL0 : ∀ B : Gˣ, algebraMap G L (B : G) ≠ 0 := fun B =>
    (map_ne_zero_iff _ (IsFractionRing.injective G L)).mpr B.ne_zero
  have hνu' : ∀ k, ν' (e (u k)) = basisValue k := fun k => by
    change ν (e.symm (e (u k))) = _
    rw [e.symm_apply_apply]
    exact hνu k
  /- Step 1: every index is a member (rank argument). -/
  have hMuniv : M = Finset.univ := by
    have hz : ∀ j, ∃ (z : O) (B : Gˣ), j ∈ M → schemeNativeStalkGerm g n p z = B * w j := by
      intro j
      by_cases hj : j ∈ M
      · obtain ⟨z, B, hzB⟩ := exists_algebraic_localEquation EV p (hH j hj) (ℓ j) (hℓ j)
          (hℓmem j hj) (hℓgen j hj) (hw0 j)
        exact ⟨z, B, fun _ => hzB⟩
      · exact ⟨1, 1, fun h => absurd h hj⟩
    choose z B hzB using hz
    have hz0 : ∀ j ∈ M, z j ≠ 0 := fun j hj h => by
      have h1 := hzB j hj
      rw [h, map_zero] at h1
      exact hw0 j ((Units.mul_right_eq_zero (B j)).mp h1.symm)
    let P : Fin n → V.functionField := fun k =>
      ∏ j ∈ M, (algebraMap O V.functionField (z j)) ^ (a k j)
    have hP0 : ∀ k, P k ≠ 0 := fun k => Finset.prod_ne_zero_iff.mpr fun j hj =>
      zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hz0 j hj))
    have hPgerm : ∀ k, schemeNativeFunctionFieldGerm g n p (P k) =
        ∏ j ∈ M, (algebraMap G L (B j : G) * algebraMap G L (w j)) ^ (a k j) := fun k => by
      simp only [P, map_prod, map_zpow₀]
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [schemeNativeFunctionFieldGerm_stalk, hzB j hj, map_mul]
    have hprodM : ∀ k, ∏ j, (algebraMap G L (w j)) ^ (a k j) =
        ∏ j ∈ M, (algebraMap G L (w j)) ^ (a k j) := fun k => by
      refine (Finset.prod_subset (Finset.subset_univ M) fun j _ hj => ?_).symm
      rw [haM k j hj, zpow_zero]
    let η' : Fin n → Gˣ := fun k => η k * ∏ j ∈ M, (B j) ^ (-a k j)
    have hε : ∀ k, ∃ ε : Oˣ, algebraMap O V.functionField (ε : O) = e (u k) / P k := fun k => by
      refine exists_unit_algebraMap_eq_of_map_eq (K := V.functionField) (L := L) hinj hff _
        (η' k) ?_
      rw [← hΓ]
      have hPL : schemeNativeFunctionFieldGerm g n p (P k) ≠ 0 :=
        (map_ne_zero_iff _ (schemeNativeFunctionFieldGerm g n p).injective).mpr (hP0 k)
      rw [map_div₀, div_eq_iff hPL, hu k, hPgerm k]
      change _ * ∏ j, (algebraMap G L (w j)) ^ (a k j) = _
      rw [hprodM k]
      simp only [η', Units.val_mul, Units.coe_prod, map_mul, map_prod, algebraMap_units_zpow,
        mul_zpow, Finset.prod_mul_distrib]
      rw [mul_assoc, ← mul_assoc (∏ j ∈ M, (algebraMap G L (B j : G)) ^ (-a k j))]
      rw [← Finset.prod_mul_distrib]
      have hone : ∀ j, (algebraMap G L (B j : G)) ^ (-a k j) *
          (algebraMap G L (B j : G)) ^ (a k j) = 1 := fun j => by
        rw [← zpow_add₀ (hBL0 (B j)), neg_add_cancel, zpow_zero]
      simp only [hone, Finset.prod_const_one, one_mul]
      rfl
    choose ε hε using hε
    have hzval : ∀ j ∈ M, ∃ c : Lex (Fin n → ℤ),
        ν' (algebraMap O V.functionField (z j)) = (c : WithTop (Lex (Fin n → ℤ))) := by
      intro j hj
      have hne : ν' (algebraMap O V.functionField (z j)) ≠ ⊤ := by
        rw [ne_eq, AddValuation.top_iff]
        exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hz0 j hj)
      exact WithTop.ne_top_iff_exists.mp hne |>.imp fun c hc => hc.symm
    choose! c hc using hzval
    have hek : ∀ k, (toLex (Pi.single k (1 : ℤ)) : Lex (Fin n → ℤ)) =
        ∑ j ∈ M, a k j • c j := fun k => by
      have h1 := hνu' k
      have h2 : e (u k) = algebraMap O V.functionField (ε k : O) * P k := by
        rw [hε k, div_mul_cancel₀ _ (hP0 k)]
      rw [h2, AddValuation.map_mul, val_eq_zero_of_isUnit ν' hcent.1 (ε k).isUnit, zero_add,
        val_prod_zpow_eq ν' M _ c hc] at h1
      exact (WithTop.coe_injective h1).symm
    apply Finset.eq_univ_of_card
    apply le_antisymm (Finset.card_le_univ M)
    rw [Fintype.card_fin]
    refine card_le_of_mul_eq_one (fun k j => a k j) (fun j l => ofLex (c j) l) ?_
    have hof : ∀ (s : Finset (Fin n)) (f : Fin n → Lex (Fin n → ℤ)),
        ofLex (∑ j ∈ s, f j) = ∑ j ∈ s, ofLex (f j) := by
      intro s f
      induction s using Finset.induction_on with
      | empty => rfl
      | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, ofLex_add, ih]
    ext k l
    have h := congrArg (fun x : Lex (Fin n → ℤ) => ofLex x l) (hek k)
    simp only [ofLex_toLex, hof, ofLex_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    change ∑ j : M, a k j * ofLex (c j) l = _
    rw [Finset.sum_coe_sort M (fun j => a k j * ofLex (c j) l), ← h, Pi.single_apply]
    simp only [eq_comm]
  refine ⟨hMuniv, ?_⟩
  subst hMuniv
  /- Step 2: algebraic local equations (Chow) and strict normal crossings coordinates. -/
  have hz : ∀ j, ∃ (z : O) (B : Gˣ), schemeNativeStalkGerm g n p z = B * w j :=
    fun j => exists_algebraic_localEquation EV p (hH j (Finset.mem_univ j)) (ℓ j) (hℓ j)
      (hℓmem j (Finset.mem_univ j)) (hℓgen j (Finset.mem_univ j)) (hw0 j)
  choose z B hzB using hz
  have hm : Ideal.span (Set.range (stalkToModel g n p ∘ z)) =
      maximalIdeal (HolGerm (ComplexModel n)) := by
    have h1 : (stalkToModel g n p ∘ z) = fun j =>
        ((Units.map (NativeHolGerm.chartEquiv p).toMonoidHom (B j) :
          (HolGerm (ComplexModel n))ˣ) : HolGerm (ComplexModel n)) *
          NativeHolGerm.chartEquiv p (w j) := by
      funext j
      change NativeHolGerm.chartEquiv p (schemeNativeStalkGerm g n p (z j)) = _
      rw [hzB j, map_mul]
      rfl
    rw [h1, span_range_units_mul]
    exact hcoord
  have hsnc := isSNCCoordinates_of_analyticCoordinates z hm
  have hz0 : ∀ j, z j ≠ 0 := fun j h => by
    have h1 := hzB j
    rw [h, map_zero] at h1
    exact hw0 j ((Units.mul_right_eq_zero (B j)).mp h1.symm)
  /- Step 3: the `u_k` are units times monomials in `z` with natural exponents. -/
  let P : Fin n → V.functionField := fun k => ∏ j, (algebraMap _ V.functionField (z j)) ^ (a k j)
  have hP0 : ∀ k, P k ≠ 0 := fun k => Finset.prod_ne_zero_iff.mpr fun j _ =>
    zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hz0 j))
  have hPgerm : ∀ k, schemeNativeFunctionFieldGerm g n p (P k) =
      ∏ j, (algebraMap G L (B j : G) * algebraMap G L (w j)) ^ (a k j) := fun k => by
    simp only [P, map_prod, map_zpow₀]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [schemeNativeFunctionFieldGerm_stalk, hzB j, map_mul]
  let η' : Fin n → Gˣ := fun k => η k * ∏ j, (B j) ^ (-a k j)
  have hε : ∀ k, ∃ ε : Oˣ, algebraMap _ V.functionField (ε : O) = e (u k) / P k := fun k => by
    refine exists_unit_algebraMap_eq_of_map_eq (K := V.functionField) (L := L) hinj hff _
      (η' k) ?_
    rw [← hΓ]
    have hPL : schemeNativeFunctionFieldGerm g n p (P k) ≠ 0 :=
      (map_ne_zero_iff _ (schemeNativeFunctionFieldGerm g n p).injective).mpr (hP0 k)
    rw [map_div₀, div_eq_iff hPL, hu k, hPgerm k]
    simp only [η', Units.val_mul, Units.coe_prod, map_mul, map_prod, algebraMap_units_zpow,
      mul_zpow, Finset.prod_mul_distrib]
    rw [mul_assoc, ← mul_assoc (∏ j, (algebraMap G L (B j : G)) ^ (-a k j))]
    rw [← Finset.prod_mul_distrib]
    have hone : ∀ j, (algebraMap G L (B j : G)) ^ (-a k j) *
        (algebraMap G L (B j : G)) ^ (a k j) = 1 := fun j => by
      rw [← zpow_add₀ (hBL0 (B j)), neg_add_cancel, zpow_zero]
    simp only [hone, Finset.prod_const_one, one_mul]
    rfl
  choose ε hε using hε
  have hlaurent : ∀ k, e (u k) = algebraMap _ V.functionField (ε k : O) *
      ∏ j, (algebraMap _ V.functionField (z j)) ^ (a k j) := fun k => by
    change e (u k) = _ * P k
    rw [hε k, div_mul_cancel₀ _ (hP0 k)]
  -- `u_k` is regular at `x`: `u_k⁻¹` regular would give `ν(u_k⁻¹) = -e_k ≥ 0`
  have hreg' : ∀ k, ∃ r : O, algebraMap _ V.functionField r = e (u k) := by
    intro k
    rcases hreg k with ⟨h, hh⟩ | ⟨h, hh⟩
    · rw [hΓ] at hh
      exact exists_algebraMap_eq_of_map_eq (K := V.functionField) (L := L) hinj hff _ h hh
    · exfalso
      rw [hΓ] at hh
      obtain ⟨r, hr⟩ :=
        exists_algebraMap_eq_of_map_eq (K := V.functionField) (L := L) hinj hff _ h hh
      have h0 := hcent.1 r
      rw [hr] at h0
      have hu0 : e (u k) ≠ 0 := by
        intro h0'
        have := hνu' k
        rw [h0', AddValuation.map_zero] at this
        exact WithTop.top_ne_coe this
      have hsum : ν' (e (u k)) + ν' (e (u k))⁻¹ = 0 := by
        rw [← AddValuation.map_mul, mul_inv_cancel₀ hu0, AddValuation.map_one]
      rw [hνu' k] at hsum
      obtain ⟨w', hw'⟩ := WithTop.ne_top_iff_exists.mp (show ν' (e (u k))⁻¹ ≠ ⊤ from by
        intro ht
        rw [ht, WithTop.add_top] at hsum
        exact WithTop.top_ne_coe hsum)
      rw [← hw'] at hsum h0
      have h1 : (toLex (Pi.single k (1 : ℤ)) : Lex (Fin n → ℤ)) + w' = 0 :=
        WithTop.coe_injective hsum
      have h2 : (0 : Lex (Fin n → ℤ)) ≤ w' := WithTop.coe_le_coe.mp h0
      have h3 : (0 : Lex (Fin n → ℤ)) < toLex (Pi.single k (1 : ℤ)) := by
        refine (OF11.lex_pos_iff _).mpr ⟨k, fun j hj => ?_, by simp⟩
        simp [hj.ne]
      have := add_pos_of_pos_of_nonneg h3 h2
      rw [h1] at this
      exact lt_irrefl _ this
  choose r hr using hreg'
  have hb : ∀ k, ∃ b : Fin n → ℕ, r k = ε k * ∏ j, z j ^ b j := fun k =>
    OF11.exists_nat_exponents_of_laurent hsnc (r k) (ε k) (a k) ((hr k).trans (hlaurent k))
  choose b hb using hb
  /- Step 4: the order `σ` (monomial cone). -/
  let c : Fin n → Fin n → ℤ := fun j => ofLex ((ν' (algebraMap _ V.functionField (z j))).untopD 0)
  have hzval : ∀ j, ν' (algebraMap _ V.functionField (z j)) =
      ((toLex (c j) : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ))) := by
    intro j
    have hne : ν' (algebraMap _ V.functionField (z j)) ≠ ⊤ := by
      rw [ne_eq, AddValuation.top_iff]
      exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hz0 j)
    obtain ⟨w', hw'⟩ := WithTop.ne_top_iff_exists.mp hne
    change _ = ((toLex (ofLex ((ν' (algebraMap _ V.functionField (z j))).untopD 0)) :
      Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ)))
    rw [← hw', WithTop.untopD_coe, toLex_ofLex]
  have hzmem : ∀ j, z j ∈ maximalIdeal O := by
    intro j
    rw [← hsnc.1]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hzpos : ∀ j, (0 : Lex (Fin n → ℤ)) < toLex (c j) := by
    intro j
    have h := hcent.2 (z j) (hzmem j)
    rw [hzval j] at h
    exact WithTop.coe_lt_coe.mp h
  have hεv : ∀ k, ν' (algebraMap _ V.functionField ((ε k : O))) = 0 :=
    fun k => val_eq_zero_of_isUnit ν' hcent.1 (ε k).isUnit
  obtain ⟨σ, hσ⟩ := OF11.exists_perm_isUnitUpperTriangular_of_monomial ν' z r
    (fun k => (ε k : O)) c hzval hzpos hεv b hb (fun k => by rw [hr k]; exact hνu' k)
  exact ⟨z, B, σ, hzB, hsnc, hσ⟩

end Scheme

end SGPT.Okounkov.OF15

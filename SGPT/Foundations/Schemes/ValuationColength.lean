import SGPT.Foundations.Schemes.ValuationIdeals
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Length
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The radical and finite colength of actual valuation ideals

For every positive real threshold the radical of its actual valuation ideal
is precisely the positive-valuation prime. When the valuation is centered at
the closed point of a Noetherian local ring, its threshold quotients are
Artinian. The center hypothesis identifies an actual prime with the maximal
ideal; finite colength is derived rather than supplied as weight data.
-/

namespace SGPT.Foundations.Schemes

variable {R F : Type*} [CommRing R] [Field F]

/-- All positive thresholds have the same radical, the actual valuation center. -/
theorem valuationIdeal_radical (v : AddValuation F (WithTop ℝ)) (f : R →+* F)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r)) {a : ℝ} (ha : 0 < a) :
    (valuationIdeal v f hcenter a).radical = positiveValuationIdeal v f hcenter := by
  ext r
  rw [Ideal.mem_radical_iff, mem_positiveValuationIdeal]
  constructor
  · rintro ⟨n, hn⟩
    by_contra h
    have hz : v (f r) = 0 := le_antisymm (not_lt.mp h) (hcenter r)
    change (a : WithTop ℝ) ≤ v (f (r ^ n)) at hn
    rw [map_pow, v.map_pow, hz, nsmul_zero] at hn
    exact (not_le.mpr ha) (WithTop.coe_le_coe.mp hn)
  · intro hr
    cases hvr : v (f r) with
    | top =>
      refine ⟨1, ?_⟩
      simp [mem_valuationIdeal, hvr]
    | coe t =>
      have ht : 0 < t := WithTop.coe_lt_coe.mp (by simpa [hvr] using hr)
      obtain ⟨n, hn⟩ := exists_nat_gt (a / t)
      refine ⟨n, ?_⟩
      change (a : WithTop ℝ) ≤ v (f (r ^ n))
      rw [map_pow, v.map_pow, hvr, ← WithTop.coe_nsmul]
      apply WithTop.coe_le_coe.mpr
      simpa only [nsmul_eq_mul] using (div_lt_iff₀ ht).mp hn |>.le

/-- Centeredness at the local closed point forces the actual threshold quotient
to be Artinian; this is not assumed as a colength hypothesis. -/
theorem valuationIdeal_quotient_isArtinian [IsNoetherianRing R] [IsLocalRing R]
    (v : AddValuation F (WithTop ℝ)) (f : R →+* F)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r))
    (hclosed : positiveValuationIdeal v f hcenter = IsLocalRing.maximalIdeal R)
    {a : ℝ} (ha : 0 < a) :
    IsArtinianRing (R ⧸ valuationIdeal v f hcenter a) := by
  apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
  rw [← Ideal.radical_minimalPrimes, valuationIdeal_radical v f hcenter ha, hclosed,
    Ideal.minimalPrimes_eq_subsingleton_self]
  exact Set.mem_singleton _

/-- The actual module colength; unlike a prescribed dimension this depends on
the quotient by the literal valuation ideal. -/
noncomputable def valuationColength (v : AddValuation F (WithTop ℝ)) (f : R →+* F)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r)) (a : ℝ) : ℕ∞ :=
  Module.length R (R ⧸ valuationIdeal v f hcenter a)

/-- Noetherian local centered valuation ideals have finite actual colength. -/
theorem valuationColength_ne_top [IsNoetherianRing R] [IsLocalRing R]
    (v : AddValuation F (WithTop ℝ)) (f : R →+* F)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r))
    (hclosed : positiveValuationIdeal v f hcenter = IsLocalRing.maximalIdeal R)
    {a : ℝ} (ha : 0 < a) : valuationColength v f hcenter a ≠ ⊤ := by
  let I := valuationIdeal v f hcenter a
  have : IsArtinianRing (R ⧸ I) := valuationIdeal_quotient_isArtinian v f hcenter hclosed ha
  have : IsArtinian R (R ⧸ I) :=
    isArtinian_of_surjective_algebraMap (R := R ⧸ I) (S := R) (M := R ⧸ I)
      Ideal.Quotient.mk_surjective
  exact Module.length_ne_top

/-- Positive thresholds have positive actual colength. -/
theorem valuationColength_pos (v : AddValuation F (WithTop ℝ)) (f : R →+* F)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r)) {a : ℝ} (ha : 0 < a) :
    0 < valuationColength v f hcenter a := by
  have : Nontrivial (R ⧸ valuationIdeal v f hcenter a) :=
    Ideal.Quotient.nontrivial_iff.mpr (valuationIdeal_ne_top v f hcenter ha)
  exact Module.length_pos

/-- Nonpositive thresholds kill the whole quotient. -/
theorem valuationColength_eq_zero_of_nonpos (v : AddValuation F (WithTop ℝ))
    (f : R →+* F) (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r))
    {a : ℝ} (ha : a ≤ 0) : valuationColength v f hcenter a = 0 := by
  unfold valuationColength
  rw [(valuationIdeal_eq_top_iff v f hcenter a).mpr ha]
  exact Module.length_eq_zero

/-- The actual colength increases with the threshold, by the surjective
transition between actual ideal quotients. -/
theorem valuationColength_monotone (v : AddValuation F (WithTop ℝ))
    (f : R →+* F) (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r)) :
    Monotone (valuationColength v f hcenter) := by
  intro a b hab
  let I := valuationIdeal v f hcenter b
  let J := valuationIdeal v f hcenter a
  have hIJ : I ≤ J := valuationIdeal_antitone v f hcenter hab
  let q : R ⧸ I →ₗ[R] R ⧸ J := (Ideal.Quotient.factorₐ R hIJ).toLinearMap
  have hq : Function.Surjective q := Ideal.Quotient.factor_surjective hIJ
  exact Module.length_le_of_surjective q hq

end SGPT.Foundations.Schemes

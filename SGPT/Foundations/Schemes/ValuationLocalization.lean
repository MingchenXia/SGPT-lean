import SGPT.Foundations.Schemes.ValuationColength
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.Tactic

/-! # Actual valuation quotients at the closed center

The field map extends to the literal localization at the positive-valuation
prime. Denominators there have value zero. At a closed center they already
become units in every positive-threshold quotient, using the proved radical
identity. The local quotient and its module length are derived below.
-/

namespace SGPT.Foundations.Schemes

variable {K S F : Type*} [Field K] [CommRing S] [Field F]
  [Algebra K S] [Algebra K F]

instance instPositiveValuationIdealIsPrime
    (v : AddValuation F (WithTop ℝ)) (f : S →+* F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s)) :
    (positiveValuationIdeal v f hcenter).IsPrime :=
  positiveValuationIdeal_isPrime v f hcenter

/-- Every denominator outside the actual center has valuation exactly zero. -/
theorem valuation_denominator_eq_zero
    (v : AddValuation F (WithTop ℝ)) (f : S →+* F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s))
    (s : (positiveValuationIdeal v f hcenter).primeCompl) :
    v (f s) = 0 := by
  apply le_antisymm _ (hcenter s)
  apply not_lt.mp
  exact s.property

theorem valuation_denominator_ne_zero
    (v : AddValuation F (WithTop ℝ)) (f : S →+* F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s))
    (s : (positiveValuationIdeal v f hcenter).primeCompl) : f s ≠ 0 := by
  intro hs
  have hv := valuation_denominator_eq_zero v f hcenter s
  rw [hs, v.map_zero] at hv
  exact WithTop.top_ne_coe hv

/-- The actual extension of the section-ring map to its localization. -/
noncomputable def localizedValuationMap
    (v : AddValuation F (WithTop ℝ)) (f : S →ₐ[K] F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s)) :
    Localization.AtPrime (positiveValuationIdeal v f.toRingHom hcenter) →ₐ[K] F :=
  IsLocalization.liftAlgHom (f := f) (fun s => isUnit_iff_ne_zero.mpr
    (valuation_denominator_ne_zero v f.toRingHom hcenter s))

theorem localizedValuationMap_algebraMap
    (v : AddValuation F (WithTop ℝ)) (f : S →ₐ[K] F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s)) (s : S) :
    localizedValuationMap v f hcenter
      (algebraMap S (Localization.AtPrime (positiveValuationIdeal v f.toRingHom hcenter)) s)
        = f s := by
  exact IsLocalization.lift_eq _ s

/-- A fraction has exactly the value of its numerator, since its denominator
has value zero. -/
theorem valuation_localized_mk'
    (v : AddValuation F (WithTop ℝ)) (f : S →ₐ[K] F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s)) (x : S)
    (s : (positiveValuationIdeal v f.toRingHom hcenter).primeCompl) :
    v (localizedValuationMap v f hcenter
      (IsLocalization.mk' (Localization.AtPrime
        (positiveValuationIdeal v f.toRingHom hcenter)) x s)) = v (f x) := by
  have h := congrArg (localizedValuationMap v f hcenter)
    (IsLocalization.mk'_spec (Localization.AtPrime
      (positiveValuationIdeal v f.toRingHom hcenter)) x s)
  rw [map_mul, localizedValuationMap_algebraMap, localizedValuationMap_algebraMap] at h
  have hv := congrArg v h
  have hs : v (f s) = 0 := valuation_denominator_eq_zero v f.toRingHom hcenter s
  rw [v.map_mul, hs, add_zero] at hv
  exact hv

/-- Centeredness on the local ring follows from the original centeredness. -/
theorem localizedValuation_nonneg
    (v : AddValuation F (WithTop ℝ)) (f : S →ₐ[K] F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s)) :
    ∀ x : Localization.AtPrime (positiveValuationIdeal v f.toRingHom hcenter),
      (0 : WithTop ℝ) ≤ v (localizedValuationMap v f hcenter x) := by
  intro x
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (positiveValuationIdeal v f.toRingHom hcenter).primeCompl x
  rw [valuation_localized_mk']

  exact hcenter r


/-- The literal threshold ideal on the actual localized ring. -/
noncomputable def localizedValuationIdeal
    (v : AddValuation F (WithTop ℝ)) (f : S →ₐ[K] F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s)) (a : ℝ) :
    Ideal (Localization.AtPrime (positiveValuationIdeal v f.toRingHom hcenter)) :=
  valuationIdeal v (localizedValuationMap v f hcenter).toRingHom
    (localizedValuation_nonneg v f hcenter) a

theorem mk'_mem_localizedValuationIdeal_iff
    (v : AddValuation F (WithTop ℝ)) (f : S →ₐ[K] F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s)) (a : ℝ) (x : S)
    (s : (positiveValuationIdeal v f.toRingHom hcenter).primeCompl) :
    IsLocalization.mk' (Localization.AtPrime
      (positiveValuationIdeal v f.toRingHom hcenter)) x s ∈
        localizedValuationIdeal v f hcenter a ↔
      x ∈ valuationIdeal v f.toRingHom hcenter a := by
  change (a : WithTop ℝ) ≤ v (localizedValuationMap v f hcenter _) ↔
    (a : WithTop ℝ) ≤ v (f x)
  rw [valuation_localized_mk']

/-- The localized literal threshold agrees with extension of the original
ideal, proved by actual fraction membership. -/
theorem localizedValuationIdeal_eq_map
    (v : AddValuation F (WithTop ℝ)) (f : S →ₐ[K] F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s)) (a : ℝ) :
    localizedValuationIdeal v f hcenter a =
      (valuationIdeal v f.toRingHom hcenter a).map
        (algebraMap S (Localization.AtPrime
          (positiveValuationIdeal v f.toRingHom hcenter))) := by
  ext z
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (positiveValuationIdeal v f.toRingHom hcenter).primeCompl z
  rw [mk'_mem_localizedValuationIdeal_iff,
    IsLocalization.mk'_mem_map_algebraMap_iff]
  constructor
  · intro hx
    exact ⟨1, (positiveValuationIdeal v f.toRingHom hcenter).primeCompl.one_mem,
      by simpa using hx⟩
  · rintro ⟨t, ht, htx⟩
    have htzero : v (f t) = 0 :=
      valuation_denominator_eq_zero v f.toRingHom hcenter ⟨t, ht⟩
    change (a : WithTop ℝ) ≤ v (f (t * x)) at htx
    change (a : WithTop ℝ) ≤ v (f x)
    rwa [map_mul, v.map_mul, htzero, zero_add] at htx

/-- The positive prime of the actual extended valuation is the local maximal
ideal, proved from numerator values. -/
theorem localizedValuation_positive_eq_maximal
    (v : AddValuation F (WithTop ℝ)) (f : S →ₐ[K] F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s)) :
    positiveValuationIdeal v (localizedValuationMap v f hcenter).toRingHom
      (localizedValuation_nonneg v f hcenter) = IsLocalRing.maximalIdeal
        (Localization.AtPrime (positiveValuationIdeal v f.toRingHom hcenter)) := by
  ext z
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (positiveValuationIdeal v f.toRingHom hcenter).primeCompl z
  rw [IsLocalization.AtPrime.mk'_mem_maximal_iff
    (Localization.AtPrime (positiveValuationIdeal v f.toRingHom hcenter))
    (positiveValuationIdeal v f.toRingHom hcenter) x s]
  change (0 : WithTop ℝ) < v (localizedValuationMap v f hcenter _) ↔
    (0 : WithTop ℝ) < v (f x)
  rw [valuation_localized_mk']

/-- Outside the closed center, denominators are units in the actual
threshold quotient. No quotient equivalence is assumed. -/
theorem valuation_denominator_isUnit_quotient [IsNoetherianRing S]
    (v : AddValuation F (WithTop ℝ)) (f : S →ₐ[K] F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s))
    (hclosed : (positiveValuationIdeal v f.toRingHom hcenter).IsMaximal)
    {a : ℝ} (ha : 0 < a)
    (s : (positiveValuationIdeal v f.toRingHom hcenter).primeCompl) :
    IsUnit (Ideal.Quotient.mk (valuationIdeal v f.toRingHom hcenter a) s) := by
  let P := positiveValuationIdeal v f.toRingHom hcenter
  let I := valuationIdeal v f.toRingHom hcenter a
  let : P.IsMaximal := hclosed
  obtain ⟨n, hn⟩ := I.exists_radical_pow_le_of_fg I.radical.fg_of_isNoetherianRing
  have hrad : I.radical = P := valuationIdeal_radical v f.toRingHom hcenter ha
  rw [hrad] at hn
  have hu := Ideal.Quotient.isUnit_mk_pow_of_notMem P (n := n) s.property
  change IsUnit (Ideal.Quotient.mk I s)
  simpa only [Ideal.Quotient.factor_mk] using hu.map (Ideal.Quotient.factor hn)

set_option backward.isDefEq.respectTransparency false in
/-- Localization at the actual closed center preserves each positive
threshold quotient. The inverse is constructed by lifting the quotient map,
since all actual localization denominators have already become units. -/
noncomputable def valuationLocalizationQuotientEquiv [IsNoetherianRing S]
    (v : AddValuation F (WithTop ℝ)) (f : S →ₐ[K] F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s))
    (hclosed : (positiveValuationIdeal v f.toRingHom hcenter).IsMaximal)
    {a : ℝ} (ha : 0 < a) :
    (S ⧸ valuationIdeal v f.toRingHom hcenter a) ≃ₐ[K]
      Localization.AtPrime (positiveValuationIdeal v f.toRingHom hcenter) ⧸
        localizedValuationIdeal v f hcenter a := by
  let P := positiveValuationIdeal v f.toRingHom hcenter
  let L := Localization.AtPrime P
  let I := valuationIdeal v f.toRingHom hcenter a
  let J := localizedValuationIdeal v f hcenter a
  let q : S →ₐ[K] L ⧸ J :=
    (Ideal.Quotient.mkₐ K J).comp (IsScalarTower.toAlgHom K S L)
  have hq : ∀ x ∈ I, q x = 0 := by
    intro x hx
    change Ideal.Quotient.mk J (algebraMap S L x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change (a : WithTop ℝ) ≤ v (localizedValuationMap v f hcenter (algebraMap S L x))
    rw [localizedValuationMap_algebraMap]
    exact hx
  let forward := Ideal.Quotient.liftₐ I q hq
  have hunit : ∀ s : P.primeCompl, IsUnit ((Ideal.Quotient.mkₐ K I) s) := by
    intro s
    exact valuation_denominator_isUnit_quotient v f hcenter hclosed ha s
  let back0 : L →ₐ[K] S ⧸ I :=
    IsLocalization.liftAlgHom (f := Ideal.Quotient.mkₐ K I) hunit
  have hback : ∀ z ∈ J, back0 z = 0 := by
    intro z hz
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl z
    have hx : x ∈ I := (mk'_mem_localizedValuationIdeal_iff v f hcenter a x s).mp hz
    have hxzero : (Ideal.Quotient.mkₐ K I) x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hx
    change IsLocalization.lift hunit (IsLocalization.mk' L x s) = 0
    rw [IsLocalization.lift_mk']
    change (Ideal.Quotient.mkₐ K I) x * _ = 0
    rw [hxzero, zero_mul]
  let back := Ideal.Quotient.liftₐ J back0 hback
  refine AlgEquiv.ofAlgHom forward back ?_ ?_
  · rw [← AlgHom.cancel_right (Ideal.Quotient.mkₐ_surjective K J)]
    apply IsLocalization.algHom_ext (W := P.primeCompl) (R := K) (A := S)
    ext x
    change forward (back0 (algebraMap S L x)) = q x
    have hbackx : back0 (algebraMap S L x) = (Ideal.Quotient.mkₐ K I) x :=
      IsLocalization.lift_eq _ x
    rw [hbackx]
    rfl
  · rw [← AlgHom.cancel_right (Ideal.Quotient.mkₐ_surjective K I)]
    ext x
    change back0 (algebraMap S L x) = (Ideal.Quotient.mkₐ K I) x
    exact IsLocalization.lift_eq _ x

/-- The quotient equivalence is the ordinary map on original sections. -/
theorem valuationLocalizationQuotientEquiv_apply_mk [IsNoetherianRing S]
    (v : AddValuation F (WithTop ℝ)) (f : S →ₐ[K] F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s))
    (hclosed : (positiveValuationIdeal v f.toRingHom hcenter).IsMaximal)
    {a : ℝ} (ha : 0 < a) (s : S) :
    valuationLocalizationQuotientEquiv v f hcenter hclosed ha
      (Ideal.Quotient.mk (valuationIdeal v f.toRingHom hcenter a) s) =
      Ideal.Quotient.mk (localizedValuationIdeal v f hcenter a)
        (algebraMap S (Localization.AtPrime
          (positiveValuationIdeal v f.toRingHom hcenter)) s) := rfl

/-- The residue quotient is also preserved, with its actual scalar map. -/
noncomputable def valuationLocalizationResidueEquiv
    (v : AddValuation F (WithTop ℝ)) (f : S →ₐ[K] F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s))
    (hclosed : (positiveValuationIdeal v f.toRingHom hcenter).IsMaximal) :
    (S ⧸ positiveValuationIdeal v f.toRingHom hcenter) ≃ₐ[K]
      IsLocalRing.ResidueField (Localization.AtPrime
        (positiveValuationIdeal v f.toRingHom hcenter)) := by
  let P := positiveValuationIdeal v f.toRingHom hcenter
  let L := Localization.AtPrime P
  let : P.IsMaximal := hclosed
  refine { IsLocalization.AtPrime.equivQuotMaximalIdeal P L with commutes' := ?_ }
  intro c
  change IsLocalization.AtPrime.equivQuotMaximalIdeal P L
    (Ideal.Quotient.mk P (algebraMap K S c)) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal L) (algebraMap K L c)
  rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk,
    IsScalarTower.algebraMap_apply K S L]

/-- Units in the actual germ have value zero, so changing a regular local
frame preserves all valuation thresholds. -/
theorem valuation_localized_unit_eq_zero
    (v : AddValuation F (WithTop ℝ)) (f : S →ₐ[K] F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s))
    (u : (Localization.AtPrime (positiveValuationIdeal v f.toRingHom hcenter))ˣ) :
    v (localizedValuationMap v f hcenter u) = 0 := by
  have hu := localizedValuation_nonneg v f hcenter (u : Localization.AtPrime _)
  have hi := localizedValuation_nonneg v f hcenter (↑u⁻¹ : Localization.AtPrime _)
  have hv : v (localizedValuationMap v f hcenter u) +
      v (localizedValuationMap v f hcenter ↑u⁻¹) = 0 := by
    rw [← v.map_mul, ← map_mul]
    rw [Units.mul_inv, map_one, v.map_one]
  exact le_antisymm ((le_add_of_nonneg_right hi).trans_eq hv) hu

theorem valuation_localized_unit_mul
    (v : AddValuation F (WithTop ℝ)) (f : S →ₐ[K] F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s))
    (u : (Localization.AtPrime (positiveValuationIdeal v f.toRingHom hcenter))ˣ)
    (x : Localization.AtPrime (positiveValuationIdeal v f.toRingHom hcenter)) :
    v (localizedValuationMap v f hcenter (u * x)) =
      v (localizedValuationMap v f hcenter x) := by
  rw [map_mul, v.map_mul, valuation_localized_unit_eq_zero, zero_add]

section Length

variable {A M : Type*} [CommRing A] [IsLocalRing A] [Algebra K A]
  [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]

/-- At a rational closed point, each residue composition factor has scalar
length one. The hypothesis is bijectivity of the actual residue scalar map. -/
theorem residue_length_eq_one_of_scalar_bijective
    (hresidue : Function.Bijective (algebraMap K (IsLocalRing.ResidueField A))) :
    Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField A) = 1 := by
  have hK : Function.Surjective (algebraMap K (IsLocalRing.ResidueField K)) := by
    exact IsLocalRing.residue_surjective
  rw [← Module.length_eq_of_surjective
    (R := IsLocalRing.ResidueField K) (S := K) (M := IsLocalRing.ResidueField A) hK]
  rw [Module.length_eq_of_surjective
    (R := IsLocalRing.ResidueField A) (S := K) (M := IsLocalRing.ResidueField A)
      hresidue.surjective]
  exact Module.length_eq_one (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A)

/-- Local module length equals scalar dimension when the actual residue map
is bijective. This follows from restriction of scalars, not a supplied
colength identity. -/
theorem local_length_eq_finrank_of_residue_bijective [FiniteDimensional K M]
    (hresidue : Function.Bijective (algebraMap K (IsLocalRing.ResidueField A))) :
    Module.length A M = (Module.finrank K M : ℕ∞) := by
  have h := IsLocalRing.length_restrictScalars K A M
  rw [residue_length_eq_one_of_scalar_bijective hresidue, mul_one] at h
  rw [← h]
  exact Module.length_eq_finrank K M

end Length

/-- Noetherian closed centeredness and a rational residue field produce
finite scalar dimension of the actual original threshold quotient. -/
theorem valuationLocalization_quotient_finiteDimensional [IsNoetherianRing S]
    (v : AddValuation F (WithTop ℝ)) (f : S →ₐ[K] F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s))
    (hclosed : (positiveValuationIdeal v f.toRingHom hcenter).IsMaximal)
    {a : ℝ} (ha : 0 < a)
    (hresidue : Function.Bijective (algebraMap K (IsLocalRing.ResidueField
      (Localization.AtPrime (positiveValuationIdeal v f.toRingHom hcenter))))) :
    FiniteDimensional K (S ⧸ valuationIdeal v f.toRingHom hcenter a) := by
  let L := Localization.AtPrime (positiveValuationIdeal v f.toRingHom hcenter)
  let J := localizedValuationIdeal v f hcenter a
  have : IsArtinianRing (L ⧸ J) := valuationIdeal_quotient_isArtinian v
    (localizedValuationMap v f hcenter).toRingHom
    (localizedValuation_nonneg v f hcenter)
    (localizedValuation_positive_eq_maximal v f hcenter) ha
  have : IsArtinian L (L ⧸ J) := isArtinian_of_surjective_algebraMap
    (R := L ⧸ J) (S := L) (M := L ⧸ J) Ideal.Quotient.mk_surjective
  have hloc : Module.length L (L ⧸ J) ≠ ⊤ := Module.length_ne_top
  have hrest := IsLocalRing.length_restrictScalars K L (L ⧸ J)
  rw [residue_length_eq_one_of_scalar_bijective hresidue, mul_one] at hrest
  have hKlen : Module.length K (L ⧸ J) ≠ ⊤ := by rwa [hrest]
  have hfinite := Module.length_ne_top_iff.mp hKlen
  have : IsNoetherian K (L ⧸ J) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).1
  exact (valuationLocalizationQuotientEquiv v f hcenter hclosed ha).symm.toLinearEquiv.finiteDimensional

/-- The module length of the genuine local valuation quotient is the scalar
dimension of the original section-ring quotient. Finite dimension can be
supplied by the derived graded decomposition theorem. -/
theorem valuationLocalization_length_eq_finrank [IsNoetherianRing S]
    (v : AddValuation F (WithTop ℝ)) (f : S →ₐ[K] F)
    (hcenter : ∀ s : S, (0 : WithTop ℝ) ≤ v (f s))
    (hclosed : (positiveValuationIdeal v f.toRingHom hcenter).IsMaximal)
    {a : ℝ} (ha : 0 < a)
    (hresidue : Function.Bijective (algebraMap K (IsLocalRing.ResidueField
      (Localization.AtPrime (positiveValuationIdeal v f.toRingHom hcenter))))) :
    Module.length (Localization.AtPrime (positiveValuationIdeal v f.toRingHom hcenter))
      (Localization.AtPrime (positiveValuationIdeal v f.toRingHom hcenter) ⧸
        localizedValuationIdeal v f hcenter a) =
      (Module.finrank K (S ⧸ valuationIdeal v f.toRingHom hcenter a) : ℕ∞) := by
  let := valuationLocalization_quotient_finiteDimensional v f hcenter hclosed ha hresidue
  let E := valuationLocalizationQuotientEquiv v f hcenter hclosed ha
  let := E.toLinearEquiv.finiteDimensional
  rw [local_length_eq_finrank_of_residue_bijective hresidue,
    ← E.toLinearEquiv.finrank_eq]

end SGPT.Foundations.Schemes

import SGPT.Foundations.Analysis.Pending.HironakaG10ChowArtinReesCentre

/-! # Strict-transform radicals from source radical containments

The exponent may depend on the source witness. No uniform exponent,
Noetherian condition, or regularity of the exceptional equation is required.
The centre ideal and the target ring map are held fixed throughout.
-/
set_option autoImplicit false
namespace SGPT.Foundations.Analysis.Pending.HironakaG10StrictIdealSourceRadical
open HironakaG10ChowArtinReesCentre
variable {A R : Type*} [CommRing A] [CommRing R]

/-- A source radical containment gives a radical containment of the whole
algebraic strict-transform ideals, using an exponent for each source witness. -/
theorem strictIdeal_le_radical_of_source_le_radical
    (φ : A →+* R) (I J D : Ideal A) (G : R) (hIJ : I ≤ J.radical) :
    strictIdeal φ I D G ≤ (strictIdeal φ J D G).radical := by
  apply Ideal.span_le.mpr
  rintro z ⟨k, h, hh, heq⟩
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp (hIJ hh.1)
  apply Ideal.mem_radical_iff.mpr
  refine ⟨m, Ideal.subset_span ?_⟩
  refine ⟨k * m, h ^ m, ⟨hm, ?_⟩, ?_⟩
  · change h ^ m ∈ D ^ (k * m)
    rw [pow_mul]
    exact Ideal.pow_mem_pow hh.2 m
  · rw [map_pow, heq, mul_pow, ← pow_mul]

/-- Mutual source radical bounds identify the radicals of the full strict
ideals, for any fixed target map, centre ideal and exceptional equation. -/
theorem radical_strictIdeal_eq_of_source_radical_bounds
    (φ : A →+* R) (I J D : Ideal A) (G : R)
    (hIJ : I ≤ J.radical) (hJI : J ≤ I.radical) :
    (strictIdeal φ I D G).radical = (strictIdeal φ J D G).radical := by
  apply le_antisymm
  · have h := Ideal.radical_mono
      (strictIdeal_le_radical_of_source_le_radical φ I J D G hIJ)
    simpa only [Ideal.radical_idem] using h
  · have h := Ideal.radical_mono
      (strictIdeal_le_radical_of_source_le_radical φ J I D G hJI)
    simpa only [Ideal.radical_idem] using h

/-- In particular, mutual source radical bounds preserve all unit-ideal
and properness tests for algebraic strict transforms. -/
theorem strictIdeal_eq_top_iff_of_source_radical_bounds
    (φ : A →+* R) (I J D : Ideal A) (G : R)
    (hIJ : I ≤ J.radical) (hJI : J ≤ I.radical) :
    strictIdeal φ I D G = ⊤ ↔ strictIdeal φ J D G = ⊤ := by
  rw [← Ideal.radical_eq_top,
    radical_strictIdeal_eq_of_source_radical_bounds φ I J D G hIJ hJI,
    Ideal.radical_eq_top]

end SGPT.Foundations.Analysis.Pending.HironakaG10StrictIdealSourceRadical

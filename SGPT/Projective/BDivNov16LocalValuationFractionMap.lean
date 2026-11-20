import Mathlib.RingTheory.Valuation.ValuationRing
/-! Blueprint first: BDivNov16LocalValuationFractionMap.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.BDivNov16

theorem actual_local_valuation_fraction_map_bijective
    {R S K : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [IsDomain S] [Field K] [Algebra R S] [Algebra R K] [Algebra S K]
    [IsScalarTower R S K] [IsFractionRing R K] [IsFractionRing S K]
    [IsLocalHom (algebraMap R S)] : Function.Bijective (algebraMap R S) := by
  classical
  constructor
  · intro a b hab
    apply IsFractionRing.injective R K
    calc
      algebraMap R K a=algebraMap S K (algebraMap R S a) :=
        IsScalarTower.algebraMap_apply R S K a
      _=algebraMap S K (algebraMap R S b) := congrArg (algebraMap S K) hab
      _=algebraMap R K b := (IsScalarTower.algebraMap_apply R S K b).symm
  · intro b
    by_cases hb : b=0
    · exact ⟨0,by simpa only [map_zero] using hb.symm⟩
    obtain ⟨a,ha⟩ | ⟨a,ha⟩ := ValuationRing.isInteger_or_isInteger R (algebraMap S K b)
    · refine ⟨a,?_⟩
      apply IsFractionRing.injective S K
      exact (IsScalarTower.algebraMap_apply R S K a).symm.trans ha
    · have hbK : algebraMap S K b≠0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective S K)).mpr hb
      have hmul : algebraMap R S a*b=1 := by
        apply IsFractionRing.injective S K
        rw [map_mul,map_one,← IsScalarTower.algebraMap_apply R S K,ha,inv_mul_cancel₀ hbK]
      have huS : IsUnit (algebraMap R S a) := isUnit_iff_dvd_one.mpr ⟨b,hmul.symm⟩
      have huR : IsUnit a := huS.of_map (algebraMap R S) a
      obtain ⟨u,rfl⟩ := huR
      refine ⟨(↑(u⁻¹) : R),?_⟩
      apply mul_left_cancel₀ huS.ne_zero
      calc
        algebraMap R S (↑u : R)*algebraMap R S (↑(u⁻¹) : R)=1 := by
          rw [← map_mul]
          simp
        _=algebraMap R S (↑u : R)*b := hmul.symm
end SGPT.Projective.BDivNov16

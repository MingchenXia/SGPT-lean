import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
/-! Blueprint-first minimal runtime reuse of genuine the earlier envelope formalization finite-type
function-field dimension proofs; no duplicate mathematical progress credit. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.BDivNov16
private theorem dimension_le_integral {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) : ringKrullDim S ≤ ringKrullDim R := by
  let := f.toAlgebra
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f) fun P Q hPQ => ?_
  obtain ⟨x,hxQ,hxP⟩ := SetLike.exists_of_lt (show P.asIdeal < Q.asIdeal from hPQ)
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff (R := R) hPQ.le ⟨hxQ,hxP⟩ (hf x)
private theorem dimension_ge_integral {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim R ≤ ringKrullDim S := by
  algebraize [f]
  have : Algebra.IsIntegral R S := ⟨hf⟩
  refine iSup_le fun l => ?_
  obtain ⟨P,-,hPp,hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S) l.head.asIdeal ⊥
    (by rw [Ideal.comap_bot_of_injective (algebraMap R S) hinj]; exact bot_le)
  have : P.LiesOver l.head.asIdeal := ⟨hPc.symm⟩
  obtain ⟨L,hL,-,-⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [←hL]
  exact Order.LTSeries.length_le_krullDim L
private theorem trdeg_equal_algebraic (k A K : Type) [Field k] [CommRing A]
    [IsDomain A] [CommRing K] [NoZeroDivisors K] [Algebra k A] [Algebra k K]
    [Algebra A K] [IsScalarTower k A K] [FaithfulSMul A K] [Algebra.IsAlgebraic A K] :
    Algebra.trdeg k A = Algebra.trdeg k K := by
  have h := trdeg_add_eq k A (A := K)
  rwa [trdeg_eq_zero (R := A),add_zero] at h

theorem actualFiniteTypeFractionDimension (k A K : Type) [Field k] [CommRing A]
    [IsDomain A] [Field K] [Algebra k A] [Algebra.FiniteType k A]
    [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] :
    ∃ n : ℕ, ringKrullDim A = n ∧ Algebra.trdeg k K = n := by
  obtain ⟨n,f,hf,hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  let : Algebra P A := f.toRingHom.toAlgebra
  let : Module.Finite P A := hfin
  let : Algebra.IsIntegral P A := Algebra.IsIntegral.of_finite P A
  let : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hf
  let : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have hP : ringKrullDim P = n := by
    simp [P,MvPolynomial.ringKrullDim_of_isNoetherianRing]
  have hd : ringKrullDim A = n := by
    apply le_antisymm
    · exact (dimension_le_integral f.toRingHom (algebraMap_isIntegral_iff.mpr inferInstance)).trans_eq hP
    · exact hP ▸ dimension_ge_integral f.toRingHom (algebraMap_isIntegral_iff.mpr inferInstance) hf
  have hA : Algebra.trdeg k A = n := by
    rw [←trdeg_equal_algebraic k P A]
    simp [P]
  let : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  exact ⟨n,hd,(trdeg_equal_algebraic k A K).symm.trans hA⟩
end SGPT.Projective.BDivNov16

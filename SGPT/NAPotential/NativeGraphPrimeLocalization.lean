import SGPT.NAPotential.OpenDivisorOrderTransport

/-!
# Original divisor localization on the literal native graph algebra

Complete blueprint: `native-graph-prime-localization.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.NativeGraphPrimeLocalization

open AlgebraicGeometry CategoryTheory IsLocalRing
open SGPT.NAPotential.Berkovich OpenDivisorOrderTransport
open SGPT.NAPotential.AlgPrimes3.PrimeDivisorOver'

/-- The SAME actual local ring is localized at the SAME contracted maximal ideal
after the genuine base-ring coefficient isomorphism. -/
theorem primeLocalization_baseEquiv
    {B C R : Type} [CommRing B] [CommRing C] [CommRing R] [IsLocalRing R]
    (i : B →+* R) (e : B ≃+* C)
    (h : letI := i.toAlgebra
      IsLocalization.AtPrime R ((maximalIdeal R).comap i)) :
    letI := (i.comp e.symm.toRingHom).toAlgebra
    IsLocalization.AtPrime R ((maximalIdeal R).comap (i.comp e.symm.toRingHom)) := by
  let : Algebra B R := i.toAlgebra
  let : IsLocalization.AtPrime R ((maximalIdeal R).comap i) := h
  let : Algebra C R := (i.comp e.symm.toRingHom).toAlgebra
  let p : Ideal B := (maximalIdeal R).comap i
  let q : Ideal C := (maximalIdeal R).comap (i.comp e.symm.toRingHom)
  have hM : p.primeCompl.map e = q.primeCompl := by
    ext c
    constructor
    · rintro ⟨b, hb, rfl⟩
      change i b ∉ maximalIdeal R at hb
      change i (e.symm (e b)) ∉ maximalIdeal R
      simpa only [e.symm_apply_apply] using hb
    · intro hc
      exact ⟨e.symm c, hc, e.apply_symm_apply c⟩
  change IsLocalization q.primeCompl R
  rw [← hM]
  exact IsLocalization.isLocalization_of_base_ringEquiv p.primeCompl R e

/-- The native prime localization inherits the ORIGINAL divisor DVR structure. -/
theorem atPrime_dvr_of_localization
    {B R : Type} [CommRing B] [IsDomain B] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra B R] (p : Ideal B) [p.IsPrime]
    [IsLocalization.AtPrime R p] : IsDiscreteValuationRing (Localization.AtPrime p) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) R).symm

/-- The original divisor produces its ACTUAL prime localization on the literal graph
adjoin in `X.functionField`, and the actual native prime is a DVR prime. -/
theorem exists_nativeGraphPrimeLocalization {X : Scheme.{0}} [IsIntegral X]
    (D : PrimeDivisorOver X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (hV : D.π (genericPoint D.Y) ∈ V)
      (_ : D.π D.point ∈ V) (s : ℕ)
      (b : Fin s → X.residueField (D.π (genericPoint D.Y))),
      letI : Nonempty V := ⟨⟨D.π (genericPoint D.Y), hV⟩⟩
      let bX := fun k => originalFunctionFieldEquiv D (b k)
      ∃ iX : Algebra.adjoin Γ(X, V) (Set.range bX) →+* D.Y.presheaf.stalk D.point,
        (∀ v : Algebra.adjoin Γ(X, V) (Set.range bX),
          algebraMap (D.Y.presheaf.stalk D.point) D.Y.functionField (iX v) =
            D.pullback ((originalFunctionFieldEquiv D).symm v)) ∧
        letI := iX.toAlgebra
        IsLocalization.AtPrime (D.Y.presheaf.stalk D.point)
            ((maximalIdeal _).comap iX) ∧
          IsDiscreteValuationRing (Localization.AtPrime ((maximalIdeal _).comap iX)) := by
  obtain ⟨V, hVa, hV, hpV, s, b, i, hi, hloc⟩ :=
    GraphDivisorOrderTransport.exists_affine_generators_primeLocalization D
  refine ⟨V, hVa, hV, hpV, s, b, ?_⟩
  let : Nonempty V := ⟨⟨D.π (genericPoint D.Y), hV⟩⟩
  let := (sectionToField D V hV).toAlgebra
  let e := originalGraphAlgebraEquiv D V hV b
  let iX := i.comp e.symm.toRingHom
  refine ⟨iX, ?_, ?_⟩
  · intro v
    change algebraMap _ D.Y.functionField (i (e.symm v)) = _
    rw [hi (e.symm v)]
    apply congrArg D.pullback
    apply (originalFunctionFieldEquiv D).injective
    rw [(originalFunctionFieldEquiv D).apply_symm_apply]
    have h := originalGraphAlgebraEquiv_coe D V hV b (e.symm v)
    change (e (e.symm v) : X.functionField) =
      originalFunctionFieldEquiv D (e.symm v) at h
    rw [e.apply_symm_apply] at h
    exact h.symm
  · let : Algebra _ (D.Y.presheaf.stalk D.point) := iX.toAlgebra
    let p := (maximalIdeal (D.Y.presheaf.stalk D.point)).comap iX
    let : IsLocalization.AtPrime (D.Y.presheaf.stalk D.point) p :=
      primeLocalization_baseEquiv i e.toRingEquiv hloc
    exact ⟨inferInstance, atPrime_dvr_of_localization (R := D.Y.presheaf.stalk D.point) p⟩

end SGPT.NAPotential.NativeGraphPrimeLocalization

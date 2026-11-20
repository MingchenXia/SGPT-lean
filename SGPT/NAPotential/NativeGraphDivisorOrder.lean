import SGPT.NAPotential.NativeGraphPrimeLocalization

/-!
# Original divisor order on the literal native graph and its centre opens

Complete blueprint: `native-graph-divisor-order.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.NativeGraphDivisorOrder

open AlgebraicGeometry CategoryTheory IsLocalRing
open SGPT.NAPotential.Berkovich GraphDivisorOrderTransport OpenDivisorOrderTransport
open SGPT.NAPotential.NativeGraphPrimeLocalization
open scoped nonZeroDivisors

/-- The SAME original fraction field remains a fraction field after inserting an actual
intermediate coefficient algebra. -/
theorem fractionField_of_intermediate_algebra
    {A B K : Type} [CommRing A] [CommRing B] [Field K]
    [Algebra A B] [Algebra A K] [Algebra B K] [IsScalarTower A B K]
    [FaithfulSMul B K] [IsFractionRing A K] : IsFractionRing B K := by
  apply IsFractionRing.of_field B K
  intro g
  obtain ⟨a, b, -, hg⟩ := IsFractionRing.div_surjective (A := A) g
  refine ⟨algebraMap A B a, algebraMap A B b, ?_⟩
  simpa only [← IsScalarTower.algebraMap_apply A B K] using hg.symm

set_option maxHeartbeats 800000 in
/-- The original divisor produces its actual native graph centre and the canonical
coefficient-fixing pullback from `X.functionField`; its original normalized order is
preserved both on the native affine chart and EVERY open neighbourhood of that centre. -/
theorem exists_nativeGraphOrder_on_open {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] (D : PrimeDivisorOver X) :
    ∃ (V : X.Opens) (hVa : IsAffineOpen V) (hV : D.π (genericPoint D.Y) ∈ V)
      (_ : D.π D.point ∈ V) (s : ℕ)
      (b : Fin s → X.residueField (D.π (genericPoint D.Y))),
      letI : Nonempty V := ⟨⟨D.π (genericPoint D.Y), hV⟩⟩
      let bX := fun k => originalFunctionFieldEquiv D (b k)
      let B := Algebra.adjoin Γ(X, V) (Set.range bX)
      letI : IsNoetherianRing B := by
        let : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hVa⟩
        let : Algebra.FiniteType Γ(X, V) B :=
          Algebra.FiniteType.adjoin_of_finite (Set.finite_range bX)
        exact Algebra.FiniteType.isNoetherianRing Γ(X, V) B
      ∃ (i : B →+* D.Y.presheaf.stalk D.point) (z : Spec (.of B))
        (ψ : X.functionField ≃+* (Spec (.of B)).functionField),
        z.asIdeal = (maximalIdeal _).comap i ∧
        (∀ v : B, ψ v = StructureSheaf.toStalk B (genericPoint (Spec (.of B))) v) ∧
        IsDiscreteValuationRing ((Spec (.of B)).presheaf.stalk z) ∧
        Order.coheight z = 1 ∧
        (∀ g : X.residueField (D.π (genericPoint D.Y)),
          D.ord g = Scheme.ord (ψ (originalFunctionFieldEquiv D g)) z) ∧
        ∀ (W : (Spec (.of B)).Opens) (hzW : z ∈ W),
          letI : Nonempty W := ⟨⟨z, hzW⟩⟩
          let ψW := ψ.trans (openFunctionFieldEquiv W.ι)
          IsDiscreteValuationRing (W.toScheme.presheaf.stalk ⟨z, hzW⟩) ∧
          @Order.coheight W.toScheme (specializationPreorder W.toScheme) ⟨z, hzW⟩ = 1 ∧
          ∀ g : X.residueField (D.π (genericPoint D.Y)),
            D.ord g = Scheme.ord (ψW (originalFunctionFieldEquiv D g))
              (⟨z, hzW⟩ : W.toScheme) := by
  obtain ⟨V, hVa, hV, hpV, s, b, i, hi, hloc, -⟩ :=
    exists_nativeGraphPrimeLocalization D
  refine ⟨V, hVa, hV, hpV, s, b, ?_⟩
  let : Nonempty V := ⟨⟨D.π (genericPoint D.Y), hV⟩⟩
  let bX := fun k => originalFunctionFieldEquiv D (b k)
  let B := Algebra.adjoin Γ(X, V) (Set.range bX)
  let C : CommRingCat := .of B
  let : IsDomain C := inferInstanceAs (IsDomain B)
  let : Algebra Γ(X, V) C := inferInstanceAs (Algebra Γ(X, V) B)
  let : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hVa⟩
  let : Algebra.FiniteType Γ(X, V) C :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range bX)
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing Γ(X, V) C
  let : Algebra C X.functionField := B.val.toRingHom.toAlgebra
  let : IsScalarTower Γ(X, V) C X.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : FaithfulSMul C X.functionField :=
    (faithfulSMul_iff_algebraMap_injective C X.functionField).mpr
      (fun _ _ h => Subtype.ext h)
  let : IsFractionRing Γ(X, V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V hVa
  let : IsFractionRing C X.functionField := fractionField_of_intermediate_algebra
    (A := Γ(X, V)) (B := C) (K := X.functionField)
  let φ := D.pullback.comp (originalFunctionFieldEquiv D).symm.toRingHom
  let : Algebra C (D.Y.presheaf.stalk D.point) := i.toAlgebra
  let : Algebra C D.Y.functionField := (φ.comp B.val.toRingHom).toAlgebra
  let : IsScalarTower C (D.Y.presheaf.stalk D.point) D.Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun v => (hi v).symm
  let p : Ideal C := (maximalIdeal (D.Y.presheaf.stalk D.point)).comap i
  let : IsLocalization.AtPrime (D.Y.presheaf.stalk D.point) p := hloc
  let z : Spec C := ⟨p, inferInstance⟩
  let : Algebra C ((Spec C).presheaf.stalk z) := StructureSheaf.stalkAlgebra C z
  let : IsLocalization.AtPrime ((Spec C).presheaf.stalk z) p :=
    StructureSheaf.IsLocalization.to_stalk C z
  let : Algebra C (Spec C).functionField :=
    (StructureSheaf.toStalk C (genericPoint (Spec C))).hom.toAlgebra
  let : IsScalarTower C ((Spec C).presheaf.stalk z) (Spec C).functionField :=
    spec_stalkFunctionField_scalarTower C z
  let : IsFractionRing C (Spec C).functionField :=
    fractionField_of_primeLocalization C ((Spec C).presheaf.stalk z) (Spec C).functionField p
  obtain ⟨hDVR, hz, e, he, hord⟩ := exists_modelOrder D z p
  let ψ : X.functionField ≃ₐ[C] (Spec C).functionField :=
    IsLocalization.algEquiv (nonZeroDivisors C) X.functionField (Spec C).functionField
  have hmaps : e.toRingHom.comp ψ.toRingHom = φ := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors C)
    apply RingHom.ext
    intro v
    change e (ψ (algebraMap C X.functionField v)) = φ (algebraMap C X.functionField v)
    rw [ψ.commutes v, he v]
    rfl
  have hnative (g : X.residueField (D.π (genericPoint D.Y))) :
      e (ψ (originalFunctionFieldEquiv D g)) = D.pullback g := by
    have h := RingHom.congr_fun hmaps (originalFunctionFieldEquiv D g)
    change e (ψ (originalFunctionFieldEquiv D g)) =
      D.pullback ((originalFunctionFieldEquiv D).symm (originalFunctionFieldEquiv D g)) at h
    simpa only [RingEquiv.symm_apply_apply] using h
  have hordψ (g : X.residueField (D.π (genericPoint D.Y))) :
      D.ord g = Scheme.ord (ψ (originalFunctionFieldEquiv D g)) z := by
    rw [hord g, ← hnative g, e.symm_apply_apply]
  refine ⟨i, z, ψ.toRingEquiv, rfl, ψ.commutes, hDVR, hz, hordψ, ?_⟩
  intro W hzW
  let : Nonempty W := ⟨⟨z, hzW⟩⟩
  let u : W.toScheme := ⟨z, hzW⟩
  let : IsDiscreteValuationRing ((Spec C).presheaf.stalk (W.ι u)) := by
    change IsDiscreteValuationRing ((Spec C).presheaf.stalk z)
    exact hDVR
  let : IsDiscreteValuationRing (W.toScheme.presheaf.stalk u) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (asIso (W.ι.stalkMap u)).commRingCatIsoToRingEquiv
  refine ⟨inferInstance, coheight_eq_one_of_stalk_dvr u, fun g => ?_⟩
  rw [hordψ g]
  exact (ord_openFunctionFieldEquiv W.ι u (ψ (originalFunctionFieldEquiv D g))).symm

end SGPT.NAPotential.NativeGraphDivisorOrder

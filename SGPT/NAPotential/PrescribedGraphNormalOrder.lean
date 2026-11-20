import SGPT.NAPotential.GraphPrimeCenterImage
import SGPT.NAPotential.GraphProjectionNormalOrder

/-!
# Original divisor normal orders on a prescribed graph chart

Complete blueprint: `prescribed-graph-normal-order.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.PrescribedGraphNormalOrder

open AlgebraicGeometry CategoryTheory IsLocalRing
open SGPT.NAPotential.Berkovich GraphDivisorOrderTransport OpenDivisorOrderTransport
open SGPT.NAPotential.NativeGraphPrimeLocalization NativeGraphDivisorOrder
open SGPT.NAPotential.OriginalGraphNormalOrder SmoothDivisorNormalOrder
open scoped nonZeroDivisors

set_option maxHeartbeats 800000 in
/-- The original divisor produces its actual native graph centre and the canonical
coefficient-fixing pullback from `X.functionField`; its original normalized order is
preserved both on the native affine chart and EVERY open neighbourhood of that centre. -/
theorem exists_nativeGraphOrder_on {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] (D : PrimeDivisorOver X)
    (V : X.Opens) (hVa : IsAffineOpen V) (hpV : D.π D.point ∈ V) :
    ∃ (hV : D.π (genericPoint D.Y) ∈ V) (s : ℕ)
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
        (∀ v : B, algebraMap (D.Y.presheaf.stalk D.point) D.Y.functionField (i v) =
          D.pullback ((originalFunctionFieldEquiv D).symm v)) ∧
        z.asIdeal = (maximalIdeal _).comap i ∧
        (∀ v : B, ψ v = StructureSheaf.toStalk B (genericPoint (Spec (.of B))) v) ∧
        IsDiscreteValuationRing ((Spec (.of B)).presheaf.stalk z) ∧
        Order.coheight z = 1 ∧
        AlgPrimes3.ProjectiveGraphProjection.projection V hVa bX z = D.π D.point ∧
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
  obtain ⟨hV, s, b, i, hi, hloc, -⟩ :=
    AffineGeneratorsAtCenter.exists_nativePrimeLocalization_on D V hVa hpV
  refine ⟨hV, s, b, ?_⟩
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
  have hcenter : AlgPrimes3.ProjectiveGraphProjection.projection V hVa bX z = D.π D.point :=
    GraphPrimeCenterImage.projection_contractedPrime D V hVa hpV bX i hi
  refine ⟨i, z, ψ.toRingEquiv, hi, rfl, ψ.commutes, hDVR, hz, hcenter, hordψ, ?_⟩
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


open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.GAGA.H0S
open SGPT.Foundations.Schemes SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending DemaillyApproximantDivisorialLelong FixedGermNormalOrder

set_option maxHeartbeats 1000000 in
/-- The original divisor produces its ACTUAL native graph maps and actual normal-order
coordinates on every genuine smooth centre neighbourhood. All centre, field-order,
flattening and germ/fraction comparisons are constructed internally. -/
theorem exists_originalGraphNormalOrder_on {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] (D : PrimeDivisorOver X)
    (V : X.Opens) (hVa : IsAffineOpen V) (hpV : D.π D.point ∈ V) (m : ℕ) :
    ∃ (hV : D.π (genericPoint D.Y) ∈ V) (s : ℕ)
      (b : Fin s → X.residueField (D.π (genericPoint D.Y))),
      letI : Nonempty V := ⟨⟨D.π (genericPoint D.Y), hV⟩⟩
      let bX := fun k => originalFunctionFieldEquiv D (b k)
      let B := Algebra.adjoin Γ(X, V) (Set.range bX)
      ∃ (i : B →+* D.Y.presheaf.stalk D.point) (z : Spec (.of B))
        (ψ : X.functionField ≃+* (Spec (.of B)).functionField),
        (∀ v : B, algebraMap (D.Y.presheaf.stalk D.point) D.Y.functionField (i v) =
          D.pullback ((originalFunctionFieldEquiv D).symm v)) ∧
        z.asIdeal = (maximalIdeal _).comap i ∧
        (∀ v : B, ψ v = StructureSheaf.toStalk B (genericPoint (Spec (.of B))) v) ∧
        IsDiscreteValuationRing ((Spec (.of B)).presheaf.stalk z) ∧
        Order.coheight z = 1 ∧
        AlgPrimes3.ProjectiveGraphProjection.projection V hVa bX z = D.π D.point ∧
        ∀ (W : (Spec (.of B)).Opens) (hzW : z ∈ W),
          letI : Nonempty W := ⟨⟨z, hzW⟩⟩
          ∀ (fW : W.toScheme ⟶ Spec (.of ℂ))
            (hsm : SmoothOfRelativeDimension (m + 1) fW) (hsep : IsSeparated fW)
            (hqc : QuasiCompact fW),
            letI := hsm
            letI := hsep
            letI := hqc
            OriginalNormalOrder D fW m (⟨z, hzW⟩ : W.toScheme)
              (((originalFunctionFieldEquiv D).trans ψ).trans (openFunctionFieldEquiv W.ι)) := by
  obtain ⟨hV, s, b, i, z, ψ, hi, hzi, hψ, hDVR, hz, hcenter, -, hopen⟩ :=
    exists_nativeGraphOrder_on D V hVa hpV
  refine ⟨hV, s, b, i, z, ψ, hi, hzi, hψ, hDVR, hz, hcenter, fun W hzW => ?_⟩
  let : Nonempty W := ⟨⟨z, hzW⟩⟩
  intro fW hsm hsep hqc
  let := hsm
  let := hsep
  let := hqc
  let : Smooth fW := SmoothOfRelativeDimension.smooth (m + 1) fW
  let : IsLocallyNoetherian W.toScheme := LocallyOfFiniteType.isLocallyNoetherian fW
  let : TopologicalSpace (SchemeComplexPoint fW) := schemeAnalyticPointTopology fW
  let : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint fW) :=
    schemeAnalyticTNChartedSpace fW (m + 1)
  let : IsComplexManifold (m + 1) (SchemeComplexPoint fW) :=
    schemeAnalyticTN_isComplexManifold fW (m + 1)
  obtain ⟨-, hzWco, hordW⟩ := hopen W hzW
  obtain ⟨y, hzy, Ψ, hreg, hrat⟩ := exists_nativeNormalOrder_withFractions
    (X := W.toScheme) fW m (z := ⟨z, hzW⟩) hzWco
  let φ := ((originalFunctionFieldEquiv D).trans ψ).trans (openFunctionFieldEquiv W.ι)
  refine ⟨y, hzy, Ψ, ?_, ?_⟩
  · intro g hg
    have h := hordW (φ.symm (algebraMap _ W.toScheme.functionField g))
    change D.ord (φ.symm (algebraMap _ W.toScheme.functionField g)) =
      Scheme.ord (φ (φ.symm (algebraMap _ W.toScheme.functionField g)))
        (⟨z, hzW⟩ : W.toScheme) at h
    rw [φ.apply_symm_apply] at h
    exact h.trans (hreg g hg)
  · intro r hr
    obtain ⟨a, b, ha, hb, hfrac, hnorm⟩ := hrat (φ r)
      ((map_ne_zero_iff _ φ.injective).mpr hr)
    exact ⟨a, b, ha, hb, hfrac, (hordW r).trans hnorm⟩


open SGPT.NAPotential.GraphProjectionNormalOrder
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphStalkNaturality

private theorem originalSupportSpecializes {X : Scheme.{0}} [IsIntegral X]
    (D : PrimeDivisorOver X) (x : X) : D.π (genericPoint D.Y) ⤳ x :=
  D.isGenericPoint_image.symm ▸ genericPoint_specializes x

set_option maxHeartbeats 1200000 in
/-- Literal original-X stalk germs and ALL original nonzero rational functions acquire
the produced analytic normal orders under the ACTUAL restricted graph projection.
All field-map equalities, centres, flattenings and order comparisons are proved internally. -/
theorem exists_graphProjectionNormalOrder_on {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] (fX : X ⟶ Spec (.of ℂ)) (D : PrimeDivisorOver X)
    (V : X.Opens) (hVa : IsAffineOpen V) (hpV : D.π D.point ∈ V) (m : ℕ) :
    ∃ (hV : D.π (genericPoint D.Y) ∈ V) (s : ℕ)
      (b : Fin s → X.residueField (D.π (genericPoint D.Y))),
      letI : Nonempty V := ⟨⟨D.π (genericPoint D.Y), hV⟩⟩
      let bX := fun k => originalFunctionFieldEquiv D (b k)
      let B := Algebra.adjoin Γ(X, V) (Set.range bX)
      ∃ (i : B →+* D.Y.presheaf.stalk D.point) (z : Spec (.of B)),
        (∀ v : B, algebraMap (D.Y.presheaf.stalk D.point) D.Y.functionField (i v) =
          D.pullback ((originalFunctionFieldEquiv D).symm v)) ∧
        z.asIdeal = (maximalIdeal _).comap i ∧
        IsDiscreteValuationRing ((Spec (.of B)).presheaf.stalk z) ∧
        Order.coheight z = 1 ∧
        AlgPrimes3.ProjectiveGraphProjection.projection V hVa bX z = D.π D.point ∧
        ∀ (W : (Spec (.of B)).Opens) (hzW : z ∈ W),
          letI : Nonempty W := ⟨⟨z, hzW⟩⟩
          let ρ := restrictedProjection V hVa bX W
          let fW := ρ ≫ fX
          ∀ (hsm : SmoothOfRelativeDimension (m + 1) fW) (hsep : IsSeparated fW)
            (hqc : QuasiCompact fW),
            letI := hsm
            letI := hsep
            letI := hqc
            ProjectionNormalOrder D fW m (⟨z, hzW⟩ : W.toScheme) ρ
              (restrictedProjection_genericPoint V hVa bX W) := by
  obtain ⟨hV, s, b, i, z, ψ, hi, hzi, hψ, hDVR, hz, hcenter, hnorm⟩ :=
    exists_originalGraphNormalOrder_on D V hVa hpV m
  refine ⟨hV, s, b, i, z, hi, hzi, hDVR, hz, hcenter, fun W hzW => ?_⟩
  let : Nonempty V := ⟨⟨D.π (genericPoint D.Y), hV⟩⟩
  let : Nonempty W := ⟨⟨z, hzW⟩⟩
  let bX := fun k => originalFunctionFieldEquiv D (b k)
  let ρ := restrictedProjection V hVa bX W
  let hρ := restrictedProjection_genericPoint V hVa bX W
  let fW := ρ ≫ fX
  dsimp only
  intro hsm hsep hqc
  let := hsm
  let := hsep
  let := hqc
  let : TopologicalSpace (SchemeComplexPoint fW) := schemeAnalyticPointTopology fW
  let : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint fW) :=
    schemeAnalyticTNChartedSpace fW (m + 1)
  let : IsComplexManifold (m + 1) (SchemeComplexPoint fW) :=
    schemeAnalyticTN_isComplexManifold fW (m + 1)
  obtain ⟨y, hzy, Ψ, hreg, hrat⟩ := hnorm W hzW fW hsm hsep hqc
  let ψW := ψ.trans (openFunctionFieldEquiv W.ι)
  let φ := ((originalFunctionFieldEquiv D).trans ψ).trans (openFunctionFieldEquiv W.ι)
  have hF := restrictedFunctionFieldPullback_eq V hVa bX W ψ hψ
  refine ⟨y, hzy, Ψ, ?_, ?_⟩
  · intro g hg
    let y' := schemeComplexPointImage fW y
    have hs := OriginalDivisorGerm.originalFunctionFieldEquiv_specialization D (ρ y')
      (originalSupportSpecializes D (ρ y')) g
    have hn := genericPullback_stalk ρ hρ y' g
    change restrictedFunctionFieldPullback V hVa bX W
        (algebraMap (X.presheaf.stalk (ρ y')) X.functionField g) =
      algebraMap (W.toScheme.presheaf.stalk y') W.toScheme.functionField
        ((ρ.stalkMap y') g) at hn
    rw [hF] at hn
    change ψW (algebraMap (X.presheaf.stalk (ρ y')) X.functionField g) =
      algebraMap (W.toScheme.presheaf.stalk y') W.toScheme.functionField
        ((ρ.stalkMap y') g) at hn
    have hgK : algebraMap (X.presheaf.stalk (ρ y')) X.functionField g ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ X.functionField)).mpr hg
    have hgN : (ρ.stalkMap y') g ≠ 0 := by
      intro hzero
      have hne := (map_ne_zero_iff _ ψW.injective).mpr hgK
      rw [hn, hzero, map_zero] at hne
      exact hne rfl
    have hc : φ ((BerkovichPoint.specializationMap (originalSupportSpecializes D (ρ y'))).hom g) =
        algebraMap (W.toScheme.presheaf.stalk y') W.toScheme.functionField ((ρ.stalkMap y') g) := by
      change ψW (originalFunctionFieldEquiv D
        ((BerkovichPoint.specializationMap (originalSupportSpecializes D (ρ y'))).hom g)) = _
      rw [hs]
      exact hn
    have hinv := congrArg φ.symm hc
    rw [φ.symm_apply_apply] at hinv
    have ho := hreg ((ρ.stalkMap y') g) hgN
    rw [← hinv] at ho
    exact ho
  · intro r hr
    obtain ⟨a, b, ha, hb, hfrac, hord⟩ := hrat r hr
    refine ⟨a, b, ha, hb, ?_, hord⟩
    change restrictedFunctionFieldPullback V hVa bX W (originalFunctionFieldEquiv D r) = _
    rw [hF]
    exact hfrac


end SGPT.NAPotential.PrescribedGraphNormalOrder

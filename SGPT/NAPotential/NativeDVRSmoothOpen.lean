import SGPT.NAPotential.PrescribedGraphNormalOrder
import SGPT.NAPotential.RegularPrimeSmooth
import SGPT.NAPotential.SmoothAffineDimension

/-!
# Actual smooth affine centre opens of native graph schemes

Complete blueprint: `native-dvr-smooth-open.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.NativeDVRSmoothOpen

open AlgebraicGeometry CategoryTheory IsLocalRing
open SGPT.NAPotential.NativeGraphPrimeLocalization

/-- The ACTUAL structural morphism has a genuine affine smooth neighbourhood of every
native DVR point. Its structural map is the actual restricted original map. -/
theorem exists_smooth_affine_of_stalk_dvr
    (k : Type) [Field k] [PerfectField k] (B : CommRingCat.{0}) [IsDomain B]
    (f : Spec B ⟶ Spec (.of k)) [LocallyOfFiniteType f] (z : Spec B)
    [IsDiscreteValuationRing ((Spec B).presheaf.stalk z)] :
    ∃ (W : (Spec B).Opens), IsAffineOpen W ∧ z ∈ W ∧
      Smooth (W.ι ≫ f) ∧ IsSeparated (W.ι ≫ f) ∧ QuasiCompact (W.ι ≫ f) := by
  let φ : k →+* B := (Spec.preimage f).hom
  let : Algebra k B := φ.toAlgebra
  let : Algebra.FiniteType k B := by
    change (Spec.preimage f).hom.FiniteType
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    simpa only [Spec.map_preimage] using (inferInstance : LocallyOfFiniteType f)
  let : Algebra B ((Spec B).presheaf.stalk z) := StructureSheaf.stalkAlgebra B z
  let : IsLocalization.AtPrime ((Spec B).presheaf.stalk z) z.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk B z
  let : IsDiscreteValuationRing (Localization.AtPrime z.asIdeal) :=
    atPrime_dvr_of_localization (R := (Spec B).presheaf.stalk z) z.asIdeal
  obtain ⟨s, hs, hsm⟩ := RegularPrimeSmooth.exists_notMem_smooth_of_dvr k B z.asIdeal
  let W : (Spec B).Opens := PrimeSpectrum.basicOpen s
  have hWa : IsAffineOpen W := IsAffineOpen.Spec_basicOpen s
  let : IsAffine W.toScheme := hWa
  let : Algebra.Smooth k (Localization.Away s) := hsm
  let g : Spec (.of (Localization.Away s)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away s)))
  have hg : Smooth g :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      ((RingHom.smooth_algebraMap).mpr hsm)
  have hfac : W.ι ≫ f = (basicOpenIsoSpecAway s).hom ≫ g := by
    rw [← basicOpenIsoSpecAway_hom_SpecMap s, Category.assoc]
    congr 1
    rw [← Spec.map_preimage f, ← Spec.map_comp]
    rfl
  have hWsm : Smooth (W.ι ≫ f) := by
    rw [hfac]
    let : Smooth g := hg
    infer_instance
  exact ⟨W, hWa, hs, hWsm, inferInstance, inferInstance⟩

open SGPT.Foundations.Schemes
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphStalkNaturality
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphPullbackComposition

/-- Actual native generic pullback preserves the actual structural field constants. -/
theorem genericPullback_constants {k : Type} [Field k]
    {X M : Scheme.{0}} [IsIntegral X] [IsIntegral M]
    (f : X ⟶ Spec (.of k)) (ρ : M ⟶ X)
    (hρ : ρ (genericPoint M) = genericPoint X) (c : k) :
    letI := schemeFunctionFieldAlgebra f
    letI := schemeFunctionFieldAlgebra (ρ ≫ f)
    genericPullback ρ hρ (algebraMap k X.functionField c) =
      algebraMap k M.functionField c := by
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionFieldAlgebra (ρ ≫ f)
  change genericPullback ρ hρ
      (X.presheaf.germ ⊤ (genericPoint X) trivial (schemeGlobalConstants f c)) =
    M.presheaf.germ ⊤ (genericPoint M) trivial (schemeGlobalConstants (ρ ≫ f) c)
  rw [genericPullback_germ ρ hρ ⊤ trivial]
  rfl

open SGPT.NAPotential.Berkovich OpenDivisorOrderTransport
open SGPT.NAPotential.AlgPrimes3

/-- The actual native graph projection is locally of finite type, from its actual
finitely generated adjoin algebra over the prescribed original affine chart. -/
theorem graphProjection_locallyOfFiniteType {X : Scheme.{0}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] (hUa : IsAffineOpen U)
    {s : ℕ} (b : Fin s → X.functionField) :
    LocallyOfFiniteType (ProjectiveGraphProjection.projection U hUa b) := by
  let B := Algebra.adjoin Γ(X, U) (Set.range b)
  let : Algebra.FiniteType Γ(X, U) B :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range b)
  have hspec : LocallyOfFiniteType (ProjectiveGraphProjection.affineProjection U b) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      ((RingHom.finiteType_algebraMap).mpr inferInstance)
  let := hspec
  unfold ProjectiveGraphProjection.projection
  infer_instance

/-- The coefficient-fixing graph field isomorphism preserves the ACTUAL structural
field action, because it is proved to be the ACTUAL generic projection pullback. -/
def graphFunctionFieldAlgEquiv {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] (fX : X ⟶ Spec (.of k))
    (U : X.Opens) [Nonempty U] (hUa : IsAffineOpen U)
    {s : ℕ} (b : Fin s → X.functionField)
    (ψ : X.functionField ≃+* (Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b)))).functionField)
    (hψ : ∀ v : Algebra.adjoin Γ(X, U) (Set.range b),
      ψ v = StructureSheaf.toStalk (Algebra.adjoin Γ(X, U) (Set.range b))
        (genericPoint (Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b))))) v) :
    letI := schemeFunctionFieldAlgebra fX
    letI := schemeFunctionFieldAlgebra (ProjectiveGraphProjection.projection U hUa b ≫ fX)
    X.functionField ≃ₐ[k] (Spec (.of (Algebra.adjoin Γ(X, U) (Set.range b)))).functionField := by
  let := schemeFunctionFieldAlgebra fX
  let := schemeFunctionFieldAlgebra (ProjectiveGraphProjection.projection U hUa b ≫ fX)
  refine { ψ with commutes' := ?_ }
  intro c
  have hF := ProjectiveGraphProjection.functionFieldPullback_eq_of_coeff U hUa b
    ψ.toRingHom (fun a => hψ (algebraMap Γ(X, U) _ a))
  have h := genericPullback_constants fX (ProjectiveGraphProjection.projection U hUa b)
    (ProjectiveGraphProjection.projection_genericPoint U hUa b) c
  change ProjectiveGraphProjection.functionFieldPullback U hUa b
      (algebraMap k X.functionField c) = _ at h
  rw [hF] at h
  exact h

open SGPT.NAPotential.PrescribedGraphNormalOrder OriginalGraphNormalOrder GraphProjectionNormalOrder
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.GAGA.H0S
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending DemaillyApproximantDivisorialLelong FixedGermNormalOrder

private theorem originalSupportSpecializes {X : Scheme.{0}} [IsIntegral X]
    (D : PrimeDivisorOver X) (x : X) : D.π (genericPoint D.Y) ⤳ x :=
  D.isGenericPoint_image.symm ▸ genericPoint_specializes x

set_option maxHeartbeats 1200000 in
/-- On EVERY prescribed original centre chart, the original divisor produces SAME
native graph data, an ACTUAL smooth affine centre open of the correct dimension, and
ACTUAL original-stalk and signed rational normal orders under its actual projection.
Smoothness, dimension, separation, quasi-compactness, centres and coordinates are outputs. -/
theorem exists_prescribedGraph_smoothNormalOrder {X : Scheme.{0}} [IsIntegral X]
    (fX : X ⟶ Spec (.of ℂ)) (m : ℕ) [SmoothOfRelativeDimension (m + 1) fX]
    (D : PrimeDivisorOver X) (V : X.Opens) (hVa : IsAffineOpen V)
    (hpV : D.π D.point ∈ V) :
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
        ProjectiveGraphProjection.projection V hVa bX z = D.π D.point ∧
        ∃ (W : (Spec (.of B)).Opens) (_hWa : IsAffineOpen W) (hzW : z ∈ W),
          letI : Nonempty W := ⟨⟨z, hzW⟩⟩
          let ρ := restrictedProjection V hVa bX W
          let fW := ρ ≫ fX
          ∃ (hsm : SmoothOfRelativeDimension (m + 1) fW) (hsep : IsSeparated fW)
            (hqc : QuasiCompact fW),
            letI := hsm
            letI := hsep
            letI := hqc
            ProjectionNormalOrder D fW m (⟨z, hzW⟩ : W.toScheme) ρ
              (restrictedProjection_genericPoint V hVa bX W) := by
  let : Smooth fX := SmoothOfRelativeDimension.smooth (m + 1) fX
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian fX
  obtain ⟨hV, s, b, i, z, ψ, hi, hzi, hψ, hDVR, hz, hcenter, hnorm⟩ :=
    exists_originalGraphNormalOrder_on D V hVa hpV m
  let : Nonempty V := ⟨⟨D.π (genericPoint D.Y), hV⟩⟩
  let bX := fun k => originalFunctionFieldEquiv D (b k)
  let B := Algebra.adjoin Γ(X, V) (Set.range bX)
  let fG := ProjectiveGraphProjection.projection V hVa bX ≫ fX
  let : LocallyOfFiniteType (ProjectiveGraphProjection.projection V hVa bX) :=
    graphProjection_locallyOfFiniteType V hVa bX
  let : LocallyOfFiniteType fG := inferInstance
  let : IsDiscreteValuationRing ((Spec (.of B)).presheaf.stalk z) := hDVR
  obtain ⟨W, hWa, hzW, hWsm, hWsep, hWqc⟩ :=
    exists_smooth_affine_of_stalk_dvr ℂ (.of B) fG z
  let : Nonempty W := ⟨⟨z, hzW⟩⟩
  let : Smooth (W.ι ≫ fG) := hWsm
  let := schemeFunctionFieldAlgebra fX
  let := schemeFunctionFieldAlgebra fG
  have hdim := SmoothAffineDimension.smoothOpen_relativeDimension_of_functionField_equiv
    fG W fX (m + 1) (graphFunctionFieldAlgEquiv fX V hVa bX ψ hψ).symm
  let ρ := restrictedProjection V hVa bX W
  let hρ := restrictedProjection_genericPoint V hVa bX W
  let fW := ρ ≫ fX
  have hsm : SmoothOfRelativeDimension (m + 1) fW := by
    simpa only [fW, ρ, restrictedProjection, fG, Category.assoc] using hdim
  have hsep : IsSeparated fW := by
    simpa only [fW, ρ, restrictedProjection, fG, Category.assoc] using hWsep
  have hqc : QuasiCompact fW := by
    simpa only [fW, ρ, restrictedProjection, fG, Category.assoc] using hWqc
  refine ⟨hV, s, b, i, z, hi, hzi, hDVR, hz, hcenter, W, hWa, hzW, hsm, hsep, hqc, ?_⟩
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


end SGPT.NAPotential.NativeDVRSmoothOpen

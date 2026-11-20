import SGPT.NAPotential.OriginalGraphNormalOrder
import SGPT.NAPotential.OriginalDivisorGerm
import SGPT.NAPotential.ProjectiveGraphProjection
import SGPT.NAPotential.ProjectiveGraphPullbackComposition

/-!
# Original stalk orders under the actual graph projection

Complete blueprint: `graph-projection-normal-order.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.GraphProjectionNormalOrder

open AlgebraicGeometry CategoryTheory IsLocalRing
open SGPT.NAPotential.Berkovich OpenDivisorOrderTransport
open SGPT.NAPotential.OriginalGraphNormalOrder
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphStalkNaturality
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphPullbackComposition
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.GAGA.H0S
open SGPT.Foundations.Schemes SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending DemaillyApproximantDivisorialLelong FixedGermNormalOrder

private theorem stalkCongr_of_eq_hom {T : Scheme.{0}} {x y : T} (h : x = y) :
    (T.presheaf.stalkCongr (.of_eq h)).hom = eqToHom (congrArg T.presheaf.stalk h) := by
  cases h
  simp [TopCat.Presheaf.stalkCongr]

/-- The two native generic open pullbacks are the SAME actual original stalk map. -/
theorem genericPullback_open {X M : Scheme.{0}} [IsIntegral X] [IsIntegral M]
    (j : M ⟶ X) [IsOpenImmersion j] :
    genericPullback j (genericPoint_eq_of_isOpenImmersion j) =
      (openFunctionFieldEquiv j).toRingHom := by
  unfold genericPullback openFunctionFieldEquiv
  rw [stalkCongr_of_eq_hom (genericPoint_eq_of_isOpenImmersion j).symm]
  rfl

section ActualProjection

open SGPT.NAPotential.AlgPrimes3

variable {X : Scheme.{0}} [IsIntegral X] (V : X.Opens) [Nonempty V]
  (hVa : IsAffineOpen V) {s : ℕ} (b : Fin s → X.functionField)

/-- The actual native graph first projection restricted to an actual native open. -/
def restrictedProjection
    (W : (Spec (.of (Algebra.adjoin Γ(X, V) (Set.range b)))).Opens) : W.toScheme ⟶ X :=
  W.ι ≫ ProjectiveGraphProjection.projection V hVa b

theorem restrictedProjection_genericPoint
    (W : (Spec (.of (Algebra.adjoin Γ(X, V) (Set.range b)))).Opens) [Nonempty W] :
    restrictedProjection V hVa b W (genericPoint W.toScheme) = genericPoint X := by
  change ProjectiveGraphProjection.projection V hVa b (W.ι (genericPoint W.toScheme)) = _
  rw [genericPoint_eq_of_isOpenImmersion W.ι]
  exact ProjectiveGraphProjection.projection_genericPoint V hVa b

/-- The actual generic-stalk pullback of the ACTUAL restricted graph projection. -/
def restrictedFunctionFieldPullback
    (W : (Spec (.of (Algebra.adjoin Γ(X, V) (Set.range b)))).Opens) [Nonempty W] :
    X.functionField →+* W.toScheme.functionField :=
  genericPullback (restrictedProjection V hVa b W) (restrictedProjection_genericPoint V hVa b W)

/-- Only original coefficient identities are needed to identify the produced field map
with the actual native projection and its actual open restriction. -/
theorem restrictedFunctionFieldPullback_eq
    (W : (Spec (.of (Algebra.adjoin Γ(X, V) (Set.range b)))).Opens) [Nonempty W]
    (ψ : X.functionField ≃+* (Spec (.of (Algebra.adjoin Γ(X, V) (Set.range b)))).functionField)
    (hψ : ∀ v : Algebra.adjoin Γ(X, V) (Set.range b),
      ψ v = StructureSheaf.toStalk (Algebra.adjoin Γ(X, V) (Set.range b))
        (genericPoint (Spec (.of (Algebra.adjoin Γ(X, V) (Set.range b))))) v) :
    restrictedFunctionFieldPullback V hVa b W =
      (ψ.trans (openFunctionFieldEquiv W.ι)).toRingHom := by
  have hP := ProjectiveGraphProjection.functionFieldPullback_eq_of_coeff V hVa b
    ψ.toRingHom (fun a => hψ (algebraMap Γ(X, V) _ a))
  unfold restrictedFunctionFieldPullback restrictedProjection
  rw [genericPullback_comp (ProjectiveGraphProjection.projection V hVa b) W.ι
    (ProjectiveGraphProjection.projection_genericPoint V hVa b)
    (genericPoint_eq_of_isOpenImmersion W.ι), genericPullback_open W.ι]
  change (openFunctionFieldEquiv W.ι).toRingHom.comp
      (ProjectiveGraphProjection.functionFieldPullback V hVa b) = _
  rw [hP]
  rfl

end ActualProjection

private theorem originalSupportSpecializes {X : Scheme.{0}} [IsIntegral X]
    (D : PrimeDivisorOver X) (x : X) : D.π (genericPoint D.Y) ⤳ x :=
  D.isGenericPoint_image.symm ▸ genericPoint_specializes x

/-- This OUTPUT target uses the actual projection's local and generic maps throughout.
No arbitrary chosen field map occurs in either original-germ or original-function order. -/
def ProjectionNormalOrder {X T : Scheme.{0}} [IsIntegral X] [IsIntegral T]
    (D : PrimeDivisorOver X) (f : T ⟶ Spec (.of ℂ)) (m : ℕ)
    [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]
    (z : T) (ρ : T ⟶ X) (hρ : ρ (genericPoint T) = genericPoint X) : Prop :=
  letI : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
  letI : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
    schemeAnalyticTNChartedSpace f (m + 1)
  letI : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
    schemeAnalyticTN_isComplexManifold f (m + 1)
  ∃ y : SchemeComplexPoint f, z ⤳ schemeComplexPointImage f y ∧
    ∃ Ψ : DivisorFlattening (m := m) (schemeNativeAlgebraicTrace f (closure {z})) y,
      (∀ g : X.presheaf.stalk (ρ (schemeComplexPointImage f y)), g ≠ 0 →
        D.ord ((BerkovichPoint.specializationMap
          (originalSupportSpecializes D (ρ (schemeComplexPointImage f y)))).hom g) =
          ((normalOrder Ψ (stalkToModel f (m + 1) y
            ((ρ.stalkMap (schemeComplexPointImage f y)) g))).toNat : ℤ)) ∧
      ∀ r : X.residueField (D.π (genericPoint D.Y)), r ≠ 0 →
        ∃ a b : T.presheaf.stalk (schemeComplexPointImage f y), a ≠ 0 ∧ b ≠ 0 ∧
          genericPullback ρ hρ (originalFunctionFieldEquiv D r) =
            algebraMap _ T.functionField a / algebraMap _ T.functionField b ∧
          D.ord r = ((normalOrder Ψ (stalkToModel f (m + 1) y a)).toNat : ℤ) -
            ((normalOrder Ψ (stalkToModel f (m + 1) y b)).toNat : ℤ)

set_option maxHeartbeats 1200000 in
/-- Literal original-X stalk germs and ALL original nonzero rational functions acquire
the produced analytic normal orders under the ACTUAL restricted graph projection.
All field-map equalities, centres, flattenings and order comparisons are proved internally. -/
theorem exists_graphProjectionNormalOrder {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] (fX : X ⟶ Spec (.of ℂ)) (D : PrimeDivisorOver X) (m : ℕ) :
    ∃ (V : X.Opens) (hVa : IsAffineOpen V) (hV : D.π (genericPoint D.Y) ∈ V)
      (_ : D.π D.point ∈ V) (s : ℕ)
      (b : Fin s → X.residueField (D.π (genericPoint D.Y))),
      letI : Nonempty V := ⟨⟨D.π (genericPoint D.Y), hV⟩⟩
      let bX := fun k => originalFunctionFieldEquiv D (b k)
      let B := Algebra.adjoin Γ(X, V) (Set.range bX)
      ∃ (i : B →+* D.Y.presheaf.stalk D.point) (z : Spec (.of B)),
        z.asIdeal = (maximalIdeal _).comap i ∧
        IsDiscreteValuationRing ((Spec (.of B)).presheaf.stalk z) ∧
        Order.coheight z = 1 ∧
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
  obtain ⟨V, hVa, hV, hpV, s, b, i, z, ψ, hzi, hψ, hDVR, hz, hnorm⟩ :=
    exists_originalGraphNormalOrder D m
  refine ⟨V, hVa, hV, hpV, s, b, i, z, hzi, hDVR, hz, fun W hzW => ?_⟩
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

end SGPT.NAPotential.GraphProjectionNormalOrder

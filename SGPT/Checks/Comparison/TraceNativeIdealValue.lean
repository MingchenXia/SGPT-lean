import SGPT.Checks.Comparison.TraceNativeStalkValue
import SGPT.NAPotential.DivDictValuation

/-! Actual center and ENTIRE ideal readback for the same native image point.
Blueprint: `trace-native-image-valuation.tex`.
The general separatedness/valuation-ring center lemma is a narrow source port
of `TowerAlgIdeal`; no old geometric prime realization is imported. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeImage
open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong
open scoped Topology Manifold ContDiff ENNReal

section Center
variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} [IsProper f]
/-- If a semi-valuation is `≥ 0` on `𝒪_{X,x}` (for a point `x` of its support), its centre is a
generization of `x` (valuative criterion of separatedness). -/
theorem center_specializes_of_nonneg (v : BerkovichPoint f) {x : X}
    (h : v.support ⤳ x)
    (hnn : ∀ g : X.presheaf.stalk x, 0 ≤ v.valAt ((BerkovichPoint.specializationMap h).hom g)) :
    v.center ⤳ x := by
  have hc := v.isCenter_center
  let φ : X.presheaf.stalk x ⟶ CommRingCat.of v.valuationRing :=
    CommRingCat.ofHom ((BerkovichPoint.specializationMap h).hom.codRestrict v.valuationRing
      (fun g => (v.mem_valuationRing_iff _).mpr (hnn g)))
  let L : Spec (CommRingCat.of v.valuationRing) ⟶ X := Spec.map φ ≫ X.fromSpecStalk x
  have hφ : φ ≫ BerkovichPoint.valuationRingIncl v = BerkovichPoint.specializationMap h := by
    ext g
    rfl
  have hL : Spec.map (BerkovichPoint.valuationRingIncl v) ≫ L =
      X.fromSpecResidueField v.support := by
    rw [← Category.assoc, ← Spec.map_comp, hφ, BerkovichPoint.specializationMap, Spec.map_comp,
      Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl
  let S : ValuativeCommSq f :=
    { R := v.valuationRing
      K := X.residueField v.support
      i₁ := X.fromSpecResidueField v.support
      i₂ := hc.lift ≫ f
      commSq := ⟨by rw [← hc.spec_map_incl_lift, Category.assoc]⟩ }
  have hsub : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion f S
  let l₁ : S.commSq.LiftStruct := ⟨hc.lift, hc.spec_map_incl_lift, rfl⟩
  have e1 : Spec.map (BerkovichPoint.valuationRingIncl v) ≫ L ≫ f =
      X.fromSpecResidueField v.support ≫ f := by
    rw [← Category.assoc, hL]
  have e2 : Spec.map (BerkovichPoint.valuationRingIncl v) ≫ hc.lift ≫ f =
      X.fromSpecResidueField v.support ≫ f := by
    rw [← Category.assoc, hc.spec_map_incl_lift]
  let l₂ : S.commSq.LiftStruct :=
    ⟨L, hL, BerkovichPoint.eq_of_spec_map_incl_comp v (e1.trans e2.symm)⟩
  have hl : hc.lift = L := congrArg (fun l => l.l) (Subsingleton.elim l₁ l₂)
  have hcen : v.center = L (IsLocalRing.closedPoint (CommRingCat.of v.valuationRing)) := by
    rw [← hl, hc.lift_closedPoint]
  have hmem : L (IsLocalRing.closedPoint (CommRingCat.of v.valuationRing)) ∈
      Set.range (X.fromSpecStalk x) :=
    ⟨Spec.map φ (IsLocalRing.closedPoint (CommRingCat.of v.valuationRing)), rfl⟩
  rw [Scheme.range_fromSpecStalk] at hmem
  rw [hcen]
  exact hmem

end Center

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsProper f]
local instance traceIdealImageTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceIdealImageCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceIdealImageManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable {m : ℕ} {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m+1)) Z]
  [IsComplexManifold (m+1) Z]
  (G : Z → SchemeComplexPoint f)
  (hG : ContMDiff 𝓘(ℂ, ComplexModel (m+1)) 𝓘(ℂ, ComplexModel n) ∞ G) (z : Z)
  {E : Set Z} (Φ : DivisorFlattening (m := m) E z) (t : ℝ) (ht : 0 < t)

/-- The ACTUAL center specializes to the original image point; native
non-dominance is retained and no center equality is supplied. -/
theorem nativeImagePoint_center_specializes :
    (nativeImagePoint f n G hG z Φ t ht).center ⤳ schemeComplexPointImage f (G z) :=
  center_specializes_of_nonneg _ (nativeImagePoint_support_specializes f n G hG z Φ t ht)
    (nativeImagePoint_valAt_stalk_nonneg f n G hG z Φ t ht)

/-- The value of EVERY actual whole ideal is the infimum of the SAME actual
pulled stalk-germ normal orders, on ANY prescribed affine neighborhood. -/
theorem nativeImagePoint_idealVal (U : X.affineOpens)
    (hU : schemeComplexPointImage f (G z) ∈ (U : X.Opens)) (J : X.IdealSheafData) :
    (nativeImagePoint f n G hG z Φ t ht).idealVal J =
      ⨅ r ∈ J.ideal U, ENNReal.ofReal t *
        (normalOrder Φ (stalkToPrimeGerm f n G hG z
          ((X.presheaf.germ (U : X.Opens) _ hU).hom r)) : ℝ≥0∞) := by
  have hc : (nativeImagePoint f n G hG z Φ t ht).center ∈ (U : X.Opens) :=
    (nativeImagePoint_center_specializes f n G hG z Φ t ht).mem_open (U : X.Opens).isOpen hU
  rw [BerkovichPoint.idealVal_eq_iInf_sectionVal _ J U hc]
  refine iInf_congr fun r => iInf_congr fun _ => ?_
  rw [← BerkovichPoint.valAt_specializationMap_germ _
    (nativeImagePoint_support_specializes f n G hG z Φ t ht) _ hU r]
  exact nativeImagePoint_toENNReal_stalk f n G hG z Φ t ht _

/-- EXACT original literal holomorphic-function order, with the SAME
actual flattening and whole algebraic stalk map. -/
theorem stalkToPrimeGerm_normalOrder_eq_functionNormalOrder
    (a : X.presheaf.stalk (schemeComplexPointImage f (G z)))
    {u : SchemeComplexPoint f → ℂ} (hu : HolomorphicAt n u (G z))
    (ha : schemeNativeStalkGerm f n (G z) a = NativeHolGerm.mk u hu) :
    normalOrder Φ (stalkToPrimeGerm f n G hG z a) =
      functionNormalOrder Φ (u ∘ G) (hu.comp_contMDiff (Eventually.of_forall fun w => hG w)) := by
  rw [stalkToPrimeGerm_mk f n G hG z a hu ha]
  rfl

end SGPT.NAPotential.TraceComparison.NativeImage

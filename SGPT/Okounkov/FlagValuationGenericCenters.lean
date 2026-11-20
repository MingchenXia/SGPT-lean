import SGPT.Okounkov.FlagValuationSchemeChowFunctions
import SGPT.Okounkov.AdmissibleFlag

/-!
# Actual coarsened centres and their original endpoint prime ideals

Nonnegativity on the original endpoint stalk constructs a genuine
`Spec R_v → Spec O_x → X`; the actual produced centre therefore generizes
the original endpoint. Its generization ideal is exactly positivity on
that original stalk, using the actual localized centre ring and its units.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry Topology IsLocalRing Set Filter SGPT.Foundations.Schemes
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open AlgebraicValuation

section Centre

variable {X : Scheme.{0}} [IsIntegral X] {k : ℕ}

/-- Nonnegativity on a genuine original stalk places the actual produced
valuation centre among its original generizations. -/
theorem valuationCenter_specializes_of_stalk_nonneg
    (f : X ⟶ Spec (.of ℂ)) [IsProper f]
    (v : AddValuation X.functionField (WithTop (Lex (Fin k → ℤ)))) (x : X)
    (hx : ∀ a : X.presheaf.stalk x, 0 ≤ v (algebraMap _ X.functionField a)) :
    valuationCenter f v ⤳ x := by
  let R := valuationRing v
  have hsp : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  let φ : X.presheaf.stalk x ⟶ CommRingCat.of R :=
    CommRingCat.ofHom ((X.presheaf.stalkSpecializes hsp).hom.codRestrict (valuationRing v) hx)
  let L : Spec (CommRingCat.of R) ⟶ X := Spec.map φ ≫ X.fromSpecStalk x
  have hφ : φ ≫ valuationRingIncl v = X.presheaf.stalkSpecializes hsp := by
    ext a
    rfl
  have hL : Spec.map (valuationRingIncl v) ≫ L = X.fromSpecStalk (genericPoint X) := by
    dsimp only [L]
    rw [← Category.assoc, ← Spec.map_comp, hφ,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  let c : X := L (closedPoint (CommRingCat.of R))
  let ψ : X.presheaf.stalk c ⟶ CommRingCat.of R := Scheme.stalkClosedPointTo L
  have hψL : Spec.map ψ ≫ X.fromSpecStalk c = L := Scheme.Spec_stalkClosedPointTo_fromSpecStalk L
  have hcsp : genericPoint X ⤳ c := (genericPoint_spec X).specializes trivial
  have hψ : ψ ≫ valuationRingIncl v = X.presheaf.stalkSpecializes hcsp := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk c)).mp
    rw [Spec.map_comp, Category.assoc, hψL, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact hL
  have hc : IsValuationCenter v c := by
    constructor
    · intro a
      have hh := (ψ.hom a).2
      change 0 ≤ v ((X.presheaf.stalkSpecializes hcsp).hom a)
      rw [← hψ]
      exact hh
    · intro a ha
      change 0 < v ((X.presheaf.stalkSpecializes hcsp).hom a)
      rw [← hψ]
      change 0 < v ((ψ.hom a : R) : X.functionField)
      rw [← mem_maximalIdeal_valuationRing]
      exact map_nonunit ψ.hom a ha
  have heq : c = valuationCenter f v :=
    hc.unique f (isValuationCenter_valuationCenter f v)
  rw [← heq]
  have hmem : c ∈ Set.range (X.fromSpecStalk x) :=
    ⟨Spec.map φ (closedPoint (CommRingCat.of R)), rfl⟩
  rwa [Scheme.range_fromSpecStalk] at hmem

/-- At a true valuation centre, positivity is exactly membership of the
actual maximal ideal; native centre-ring units have actual value zero. -/
theorem isValuationCenter_pos_iff_mem_maximalIdeal
    {v : AddValuation X.functionField (WithTop (Lex (Fin k → ℤ)))} {c : X}
    (hc : IsValuationCenter v c) (a : X.presheaf.stalk c) :
    0 < v (algebraMap _ X.functionField a) ↔ a ∈ maximalIdeal (X.presheaf.stalk c) := by
  constructor
  · intro hpos
    by_contra hnot
    have ha : IsUnit a := by simpa only [mem_maximalIdeal, mem_nonunits_iff, not_not] using hnot
    have hz := (isUnit_valuationRing_iff v (hc.stalkHom.hom a)).mp (ha.map hc.stalkHom.hom)
    change v (algebraMap _ X.functionField a) = 0 at hz
    rw [hz] at hpos
    exact lt_irrefl _ hpos
  · exact hc.2 a

/-- The prime cut out by a genuine generization centre is exactly the
contracted positive valuation ideal on the original endpoint stalk. -/
theorem generizationIdeal_mem_iff_valuation_pos
    {v : AddValuation X.functionField (WithTop (Lex (Fin k → ℤ)))} {c x : X}
    (hc : IsValuationCenter v c) (hcx : c ⤳ x) (a : X.presheaf.stalk x) :
    a ∈ generizationIdeal hcx ↔ 0 < v (algebraMap _ X.functionField a) := by
  change (X.presheaf.stalkSpecializes hcx).hom a ∈ maximalIdeal (X.presheaf.stalk c) ↔ _
  rw [← isValuationCenter_pos_iff_mem_maximalIdeal hc]
  have hcomp : algebraMap (X.presheaf.stalk c) X.functionField
      ((X.presheaf.stalkSpecializes hcx).hom a) = algebraMap _ X.functionField a := by
    change ((X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom
      ((X.presheaf.stalkSpecializes hcx).hom a)) = _
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
    rfl
  rw [hcomp]

end Centre

section OriginalFlag

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance prefixCentreTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance prefixCentreCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance prefixCentreManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- Every actual coarsening centre of the original full flag lies among
the original endpoint's generizations; no centre point is an input. -/
theorem schemeOriginalFlagPrefixCenter_specializes_endpoint (E : ClosedProjectiveEmbedding f)
    (omega : KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
    (k : ℕ) (hk : k ≤ n) :
    letI := E.isProper
    valuationCenter f (ValCurr.prefixValuation hk
      (schemeOriginalFlagFunctionFieldValuation f n E omega Y hY)) ⤳
      schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n E omega Y hY).val := by
  let := E.isProper
  apply valuationCenter_specializes_of_stalk_nonneg
  intro a
  change 0 ≤ ValCurr.prefixWithTopHom hk
    (schemeOriginalFlagFunctionFieldValuation f n E omega Y hY _)
  rw [schemeOriginalFlagFunctionFieldValuation_stalk]
  have hh := ValCurr.monotone_prefixWithTopHom hk
    (originalFlagGermValuation_nonneg
      (schemeProjectiveOriginalFlagGeometry f n E omega Y hY)
      (schemeProjectiveOriginalFlagPoint f n E omega Y hY)
      (schemeNativeStalkGerm f n (schemeProjectiveOriginalFlagPoint f n E omega Y hY).val a))
  simpa only [map_zero] using hh

/-- Original algebraic Chow coefficients belong to the actual produced
centre's generization ideal exactly when their actual native Chow germ
vanishes on the original analytic flag member. -/
theorem schemeOriginalFlagPrefixCenter_polyCoef_mem_iff (E : ClosedProjectiveEmbedding f)
    (omega : KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
    (k : ℕ) (hk : k ≤ n) (i : Fin (E.ambientDimension + 1))
    (hi : schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n E omega Y hY).val ∈ coordOpen E i)
    (P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ) :
    letI := E.isProper
    (X.presheaf.germ (coordOpen E i)
      (schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n E omega Y hY).val)
      hi (polyCoef E i P)) ∈ generizationIdeal
        (schemeOriginalFlagPrefixCenter_specializes_endpoint f n E omega Y hY k hk) ↔
      (vanishingIdeal (n := n) (Y ⟨k, Nat.lt_succ_of_le hk⟩)).mem
        (schemeProjectiveOriginalFlagPoint f n E omega Y hY).val
        (genFun (projectivePoint f E n) i P) := by
  let := E.isProper
  rw [generizationIdeal_mem_iff_valuation_pos
    (isValuationCenter_valuationCenter f (ValCurr.prefixValuation hk
      (schemeOriginalFlagFunctionFieldValuation f n E omega Y hY)))
    (schemeOriginalFlagPrefixCenter_specializes_endpoint f n E omega Y hY k hk)]
  exact schemeOriginalFlagPrefix_polyCoef_pos_iff f E n omega Y hY k hk i hi P

end OriginalFlag

end SGPT.Okounkov

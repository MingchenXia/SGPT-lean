import SGPT.BDivisor.BD7SmoothAlgebraicIndex
import SGPT.BDivisor.BD7IntegralNumericalQuotient
import SGPT.BDivisor.BD6AlgebraicChernPullback
import SGPT.BDivisor.BDNumericalClasses
import SGPT.Okounkov.SchemeGenericPointComplexSurjectivity

/-!
# Actual transition maps on the degree-one algebraic numerical classes

The pullback is induced by the literal inverse image of scheme line bundles.
The comparison with the analytic pushforward is stated separately on the actual
prime generators, with the residue-field multiplicity of algebraic cycle theory.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD7

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy CanonicalCurrentFrame
open scoped Manifold ContDiff

local instance numericalTransitionTopology {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) :=
  schemeAnalyticPointTopology g

local instance numericalTransitionCharts {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g n

local instance numericalTransitionManifold {S : Scheme.{0}}
    (g : S ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n g]
    [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold n (SchemeComplexPoint g) :=
  schemeAnalyticTN_isComplexManifold g n

section Index

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} {d : ℕ}
  [SmoothOfRelativeDimension d f]
  {A B : SmoothAlgebraicModel f d} (h : A ≤ B)

/-- The selected algebraic transition has the literal structure equality. -/
theorem SmoothAlgebraicModel.homOfLE_structure :
    A.homOfLE h ≫ (A.p ≫ f) = B.p ≫ f := by
  rw [← Category.assoc, A.homOfLE_over h]

/-- The selected transition is proper, using the exact over-base triangle. -/
theorem SmoothAlgebraicModel.homOfLE_isProper : IsProper (A.homOfLE h) := by
  let : IsProper ((A.homOfLE h) ≫ A.p) := by
    rw [A.homOfLE_over h]
    infer_instance
  exact IsProper.of_comp (A.homOfLE h) A.p

/-- The algebraic triangle also commutes for the identical complex-point maps. -/
theorem SmoothAlgebraicModel.homOfLE_point_triangle :
    schemeComplexPointMap (A.p ≫ f) f A.p rfl ∘
      schemeComplexPointMap (B.p ≫ f) (A.p ≫ f) (A.homOfLE h)
        (SmoothAlgebraicModel.homOfLE_structure h) =
          schemeComplexPointMap (B.p ≫ f) f B.p rfl := by
  let q := A.homOfLE h
  let hq := SmoothAlgebraicModel.homOfLE_structure h
  funext z
  change schemeComplexPointMap (A.p ≫ f) f A.p rfl
    (schemeComplexPointMap (B.p ≫ f) (A.p ≫ f) q hq z) =
      schemeComplexPointMap (B.p ≫ f) f B.p rfl z
  rw [← schemeComplexPointMap_comp (B.p ≫ f) (A.p ≫ f) f q hq A.p rfl]
  apply Subtype.ext
  change z.val ≫ (q ≫ A.p) = z.val ≫ B.p
  rw [A.homOfLE_over h]

/-- The actual holomorphic map on points of the selected scheme transition. -/
theorem SmoothAlgebraicModel.homOfLE_point_contMDiff :
    ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞
      (schemeComplexPointMap (B.p ≫ f) (A.p ≫ f) (A.homOfLE h)
        (SmoothAlgebraicModel.homOfLE_structure h)) :=
  NativeOpenJacobian.schemeComplexPointMap_contMDiff_of_structure
    (A.p ≫ f) (B.p ≫ f) (A.homOfLE h) (SmoothAlgebraicModel.homOfLE_structure h) d ∞

/-- The analytic map of the actual transition is the proper bimeromorphic map over the base. -/
theorem SmoothAlgebraicModel.homOfLE_analyticModification (E : ClosedProjectiveEmbedding f) :
    letI := A.embedding.isSeparated
    letI := A.embedding.quasiCompact
    letI := B.embedding.isSeparated
    letI := B.embedding.quasiCompact
    IsAnalyticModification (n := d)
      (schemeComplexPointMap (B.p ≫ f) (A.p ≫ f) (A.homOfLE h)
        (SmoothAlgebraicModel.homOfLE_structure h)) := by
  let := E.isSeparated
  let := E.quasiCompact
  exact AnalyticModelDomination.isAnalyticModification_of_holomorphic_over
    (A.analyticModification E) (B.analyticModification E)
    (SmoothAlgebraicModel.homOfLE_point_contMDiff h)
    (SmoothAlgebraicModel.homOfLE_point_triangle h)

/-- Algebraic domination analytifies to the unique domination of the actual analytic models. -/
theorem SmoothAlgebraicModel.homOfLE_eq_analytic_homOfLE (E : ClosedProjectiveEmbedding f) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI := A.embedding.isSeparated
    letI := A.embedding.quasiCompact
    letI := B.embedding.isSeparated
    letI := B.embedding.quasiCompact
    let A' : Modification d (SchemeComplexPoint f) :=
      ⟨SchemeComplexPoint (A.p ≫ f), schemeComplexPointMap (A.p ≫ f) f A.p rfl,
        A.analyticModification E⟩
    let B' : Modification d (SchemeComplexPoint f) :=
      ⟨SchemeComplexPoint (B.p ≫ f), schemeComplexPointMap (B.p ≫ f) f B.p rfl,
        B.analyticModification E⟩
    ∃ h' : A' ≤ B',
      Modification.homOfLE h' =
        schemeComplexPointMap (B.p ≫ f) (A.p ≫ f) (A.homOfLE h)
          (SmoothAlgebraicModel.homOfLE_structure h) := by
  letI := E.isSeparated
  letI := E.quasiCompact
  letI := A.embedding.isSeparated
  letI := A.embedding.quasiCompact
  letI := B.embedding.isSeparated
  letI := B.embedding.quasiCompact
  refine ⟨⟨_, SmoothAlgebraicModel.homOfLE_point_contMDiff h,
    SmoothAlgebraicModel.homOfLE_point_triangle h⟩, ?_⟩
  exact Modification.homOfLE_eq _ (SmoothAlgebraicModel.homOfLE_point_contMDiff h)
    (SmoothAlgebraicModel.homOfLE_point_triangle h)

/-- The generic stalk isomorphism of the actual transition follows by cancellation. -/
theorem SmoothAlgebraicModel.homOfLE_genericStalk_isIso (E : ClosedProjectiveEmbedding f) :
    IsIso ((A.homOfLE h).stalkMap (genericPoint B.V)) := by
  let := A.embedding.isSeparated
  let := A.embedding.quasiCompact
  let := A.embedding.locallyOfFiniteType
  let := B.embedding.isSeparated
  let := B.embedding.quasiCompact
  let q := A.homOfLE h
  let hq := SmoothAlgebraicModel.homOfLE_structure h
  have hs : Function.Surjective
      (schemeComplexPointMap (B.p ≫ f) (A.p ≫ f) q hq) :=
    AnalyticModificationStrongPullback.surjective_of_isAnalyticModification
      (SmoothAlgebraicModel.homOfLE_analyticModification h E)
  have hs' : Function.Surjective
      (schemeComplexPointMap (q ≫ (A.p ≫ f)) (A.p ≫ f) q rfl) := by
    intro z
    obtain ⟨y, hy⟩ := hs z
    refine ⟨⟨y.val, ?_⟩, ?_⟩
    · rw [hq]
      exact y.property
    · exact Subtype.ext (congrArg Subtype.val hy)
  have hη := genericPoint_eq_of_surjective_complexPoints (A.p ≫ f) q hs'
  let : IsIso (A.p.stalkMap (q (genericPoint B.V))) := by
    rw [hη]
    infer_instance
  let : IsIso ((q ≫ A.p).stalkMap (genericPoint B.V)) := by
    rw [A.homOfLE_over h]
    infer_instance
  let : IsIso (A.p.stalkMap (q (genericPoint B.V)) ≫ q.stalkMap (genericPoint B.V)) := by
    rw [← Scheme.Hom.stalkMap_comp]
    infer_instance
  exact IsIso.of_isIso_comp_left (A.p.stalkMap (q (genericPoint B.V)))
    (q.stalkMap (genericPoint B.V))

end Index

section Numerical

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  (fX : X ⟶ Spec (.of ℂ)) (fY : Y ⟶ Spec (.of ℂ))
  (EX : ClosedProjectiveEmbedding fX) (EY : ClosedProjectiveEmbedding fY)
  {m : ℕ} [SmoothOfRelativeDimension (m + 1) fX] [SmoothOfRelativeDimension (m + 1) fY]
  [IsSeparated fX] [QuasiCompact fX] [IsSeparated fY] [QuasiCompact fY]
  [ConnectedSpace (SchemeComplexPoint fX)] [ConnectedSpace (SchemeComplexPoint fY)]
  [CompactSpace (SchemeComplexPoint fX)] [CompactSpace (SchemeComplexPoint fY)]
  (hnorm : NormalizationProjectiveForCurves)

local notation "NX" => OriginalIntegralCurveDegreeQuotient_bd7 fX EX
local notation "NY" => OriginalIntegralCurveDegreeQuotient_bd7 fY EY
local notation "SX" => DFAlg.neronSeveri (m + 1) (SchemeComplexPoint fX)
local notation "SY" => DFAlg.neronSeveri (m + 1) (SchemeComplexPoint fY)
local notation "cX" => integralNumericalEquivNS_bd7 fX EX m hnorm
local notation "cY" => integralNumericalEquivNS_bd7 fY EY m hnorm

/-- Chern class of a numerical quotient generator, on the original combination. -/
theorem numericalChern_mkQ (v : CartierCombinations X) :
    ((cX ((originalIntegralCurveDegreeRelations_bd7 fX EX).mkQ v) : SX) :
      RealBottChern (m + 1) (SchemeComplexPoint fX)) = cartierChern_bd7 fX EX (m + 1) v := by
  simp only [integralNumericalEquivNS_bd7, integralNumericalEquivSmoothNumerical_bd7,
    smoothCurveNumericalEquivNS_bd7, LinearEquiv.trans_apply, Submodule.mkQ_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivRange_apply_mk, LinearEquiv.coe_ofEq_apply]

variable (q : X ⟶ Y) (hq : q ≫ fY = fX)

local notation "qh" => SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap
  fX fY q hq (m + 1) (m + 1) ∞
local notation "pullLines" => Finsupp.lmapDomain ℝ ℝ (BD6.pullbackIntrinsicLineBundle q)

include m hnorm hq in
/-- The inverse image of actual Cartier combinations sends the curve relations to curve relations. -/
theorem pullbackCartierCombinations_mem_numericalRelations
    (v : CartierCombinations Y) (hv : v ∈ originalIntegralCurveDegreeRelations_bd7 fY EY) :
    pullLines v ∈ originalIntegralCurveDegreeRelations_bd7 fX EX := by
  rw [originalIntegralCurveDegreeRelations_eq_chernKernel_bd7 fY (m + 1) EY hnorm,
    LinearMap.mem_ker] at hv
  rw [originalIntegralCurveDegreeRelations_eq_chernKernel_bd7 fX (m + 1) EX hnorm,
    LinearMap.mem_ker]
  change Finsupp.linearCombination ℝ (BD6.algChern fX EX m) (pullLines v) = 0
  rw [BD6.algChern_linearCombination_pullback fX fY q hq m EX EY]
  change classPullback qh (cartierChern_bd7 fY EY (m + 1) v) = 0
  rw [hv, map_zero]

/-- Actual numerical pullback induced by inverse image of scheme line bundles. -/
def numericalCartierPullback : NY →ₗ[ℝ] NX :=
  (originalIntegralCurveDegreeRelations_bd7 fY EY).mapQ
    (originalIntegralCurveDegreeRelations_bd7 fX EX) pullLines
    (fun v hv => pullbackCartierCombinations_mem_numericalRelations fX fY EX EY (m := m) hnorm q hq v hv)

theorem numericalCartierPullback_mkQ (v : CartierCombinations Y) :
    numericalCartierPullback fX fY EX EY (m := m) hnorm q hq
        ((originalIntegralCurveDegreeRelations_bd7 fY EY).mkQ v) =
      (originalIntegralCurveDegreeRelations_bd7 fX EX).mkQ (pullLines v) := rfl

/-- The actual algebraic numerical pullback commutes with Bott--Chern pullback. -/
theorem numericalChern_numericalCartierPullback (v : NY) :
    ((cX (numericalCartierPullback fX fY EX EY (m := m) hnorm q hq v) : SX) :
      RealBottChern (m + 1) (SchemeComplexPoint fX)) =
      classPullback qh (cY v : RealBottChern (m + 1) (SchemeComplexPoint fY)) := by
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ v
  rw [numericalCartierPullback_mkQ, numericalChern_mkQ, numericalChern_mkQ]
  change Finsupp.linearCombination ℝ (BD6.algChern fX EX m) (pullLines w) =
    classPullback qh (Finsupp.linearCombination ℝ (BD6.algChern fY EY m) w)
  exact BD6.algChern_linearCombination_pullback fX fY q hq m EX EY w

/-- Transport of the analytic pushforward. Its algebraic interpretation is a separate
prime-generator compatibility statement below. -/
def transportedAnalyticPushforward (q : X ⟶ Y) (hq : q ≫ fY = fX)
    (hmod : IsAnalyticModification (n := m + 1) (schemeComplexPointMap fX fY q hq)) :
    NX →ₗ[ℝ] NY :=
  let push : RealBottChern (m + 1) (SchemeComplexPoint fX) →ₗ[ℝ]
      RealBottChern (m + 1) (SchemeComplexPoint fY) :=
    classPushforward hmod.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
  let restricted : SX →ₗ[ℝ] SY :=
    (push.comp (SX).subtype).codRestrict SY (fun a =>
      DFAlg.classPushforward_mem_neronSeveri_of_isAnalyticModification hmod a.property)
  (cY).symm.toLinearMap.comp (restricted.comp (cX).toLinearMap)

theorem numericalChern_transportedAnalyticPushforward
    (q : X ⟶ Y) (hq : q ≫ fY = fX)
    (hmod : IsAnalyticModification (n := m + 1) (schemeComplexPointMap fX fY q hq))
    (v : NX) :
    ((cY ((transportedAnalyticPushforward (q := q) (hq := hq) (hmod := hmod)
        fX fY EX EY (m := m) hnorm) v) : SY) :
      RealBottChern (m + 1) (SchemeComplexPoint fY)) =
      classPushforward (g := schemeComplexPointMap fX fY q hq)
        hmod.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (cX v : RealBottChern (m + 1) (SchemeComplexPoint fX)) := by
  simp only [transportedAnalyticPushforward, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply]

/-- The literal algebraic coefficient: a height-one prime is contracted to zero, or is
sent to its image prime with the extension degree of the two actual residue fields. -/
def algebraicPrimeImageClass
    (primeY : {y : Y // Order.coheight y = 1} → NY)
    (x : {x : X // Order.coheight x = 1}) : NY :=
  if hy : Order.coheight (q x.val) = 1 then
    (q.residueDegree x.val : ℝ) • primeY ⟨q x.val, hy⟩
  else 0

/-- Once actual prime cycle classes span and satisfy the residue-weighted generator
formula, any algebraic pushforward satisfying that formula is the transported map. -/
theorem algebraicPushforward_eq_transported_of_prime_formula
    (q : X ⟶ Y) (hq : q ≫ fY = fX)
    (hmod : IsAnalyticModification (n := m + 1) (schemeComplexPointMap fX fY q hq))
    (primeX : {x : X // Order.coheight x = 1} → NX)
    (primeY : {y : Y // Order.coheight y = 1} → NY)
    (hspan : Submodule.span ℝ (Set.range primeX) = ⊤)
    (pushAlgebraic : NX →ₗ[ℝ] NY)
    (hpush : ∀ x, pushAlgebraic (primeX x) = algebraicPrimeImageClass fY EY q primeY x)
    (hprime : ∀ x,
      classPushforward (g := schemeComplexPointMap fX fY q hq)
          hmod.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
          (cX (primeX x) : RealBottChern (m + 1) (SchemeComplexPoint fX)) =
        (cY (algebraicPrimeImageClass fY EY q primeY x) :
          RealBottChern (m + 1) (SchemeComplexPoint fY))) :
    pushAlgebraic = (transportedAnalyticPushforward (q := q) (hq := hq) (hmod := hmod)
        fX fY EX EY (m := m) hnorm) := by
  apply LinearMap.ext
  intro a
  have ha : a ∈ Submodule.span ℝ (Set.range primeX) := by rw [hspan]; exact Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, rfl⟩ := hv
    apply (cY).injective
    apply Subtype.ext
    rw [hpush, numericalChern_transportedAnalyticPushforward]
    exact (hprime x).symm
  | zero => simp only [map_zero]
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | smul r v _ hv => rw [map_smul, map_smul, hv]

/-- The actual prime pushforward formula descends uniquely to the algebraic numerical
quotient once the prime generators span and their Bott--Chern comparison is proved. -/
theorem existsUnique_numericalPushforward_of_prime_formula
    (q : X ⟶ Y) (hq : q ≫ fY = fX)
    (hmod : IsAnalyticModification (n := m + 1) (schemeComplexPointMap fX fY q hq))
    (primeX : {x : X // Order.coheight x = 1} → NX)
    (primeY : {y : Y // Order.coheight y = 1} → NY)
    (hspan : Submodule.span ℝ (Set.range primeX) = ⊤)
    (hprime : ∀ x,
      classPushforward (g := schemeComplexPointMap fX fY q hq)
          hmod.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
          (cX (primeX x) : RealBottChern (m + 1) (SchemeComplexPoint fX)) =
        (cY (algebraicPrimeImageClass fY EY q primeY x) :
          RealBottChern (m + 1) (SchemeComplexPoint fY))) :
    ∃! L : NX →ₗ[ℝ] NY, ∀ x, L (primeX x) = algebraicPrimeImageClass fY EY q primeY x := by
  refine ⟨(transportedAnalyticPushforward (q := q) (hq := hq) (hmod := hmod)
        fX fY EX EY (m := m) hnorm), ?_, ?_⟩
  · intro x
    apply (cY).injective
    apply Subtype.ext
    rw [numericalChern_transportedAnalyticPushforward]
    exact hprime x
  · intro L hL
    exact algebraicPushforward_eq_transported_of_prime_formula
      (q := q) (hq := hq) (hmod := hmod) fX fY EX EY (m := m) hnorm
      primeX primeY hspan L hL hprime

end Numerical
end SGPT.BDivisor.BD7

import SGPT.NAPotential.FSPosImmersion
import SGPT.Okounkov.AdmissibleFlag
import SGPT.Okounkov.SchemeComplexPointStalkEvaluation

/-! Genuine point derivations on the SAME original algebraic stalk.
Blueprint: algebraic-native-stalk-derivation.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology Manifold
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.NAPotential.FSPos

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance derivationPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance derivationPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance derivationPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

local instance originalStalkComplexAlgebra (p : SchemeComplexPoint f) :
    Algebra ℂ (X.presheaf.stalk (schemeComplexPointImage f p)) :=
  stalkComplexAlgebra f (schemeComplexPointImage f p)

local instance originalPointStalkAlgebra (p : SchemeComplexPoint f) :
    Algebra (X.presheaf.stalk (schemeComplexPointImage f p)) ℂ :=
  (schemeComplexPointStalkEval f p).toAlgebra

/-- Actual preferred-chart stalk evaluation is the canonical original
point evaluation on the ENTIRE original algebraic stalk. -/
theorem stalkToModel_eval (p : SchemeComplexPoint f)
    (a : X.presheaf.stalk (schemeComplexPointImage f p)) :
    HolGerm.eval (stalkToModel f n p a) = schemeComplexPointStalkEval f p a := by
  change HolGerm.eval (NativeHolGerm.chartEquiv p (schemeNativeStalkGerm f n p a)) = _
  rw [NativeHolGerm.eval_chartEquiv, schemeNativeStalkGerm_eval]

include n in
/-- The SAME original structural constants evaluate to themselves. -/
theorem originalPointStalkEval_algebraMap (p : SchemeComplexPoint f) (c : ℂ) :
    schemeComplexPointStalkEval f p
      (algebraMap ℂ (X.presheaf.stalk (schemeComplexPointImage f p)) c) = c := by
  rw [← stalkToModel_eval f n p]
  change HolGerm.eval (stalkToModel f n p
    (X.presheaf.germ ⊤ (schemeComplexPointImage f p) trivial (schemeGlobalConstants f c))) = c
  rw [stalkToModel_constants]
  exact HolGerm.eval_constHom c

include n in
/-- Actual structural scalar compatibility at the SAME original point. -/
theorem originalPointStalk_scalarTower (p : SchemeComplexPoint f) :
    IsScalarTower ℂ (X.presheaf.stalk (schemeComplexPointImage f p)) ℂ := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (originalPointStalkEval_algebraMap f n p c).symm

/-- Native directional differentiation, restricted to the SAME entire
original algebraic stalk and its canonical original point module. -/
def nativeStalkDerivation (p : SchemeComplexPoint f) (v : ComplexModel n) :
    Derivation ℂ (X.presheaf.stalk (schemeComplexPointImage f p)) ℂ where
  toFun a := germDeriv v (stalkToModel f n p a)
  map_add' a b := by rw [map_add, germDeriv_add]
  map_smul' c a := by
    rw [Algebra.smul_def, map_mul]
    change germDeriv v (stalkToModel f n p
      (X.presheaf.germ ⊤ (schemeComplexPointImage f p) trivial (schemeGlobalConstants f c)) *
        stalkToModel f n p a) = c * germDeriv v (stalkToModel f n p a)
    rw [stalkToModel_constants, germDeriv_mul, germDeriv_algebraMap,
      mul_zero, add_zero]
    change HolGerm.eval (HolGerm.constHom c) * _ = _
    rw [HolGerm.eval_constHom]
  map_one_eq_zero' := by
    change germDeriv v (stalkToModel f n p 1) = 0
    rw [map_one, germDeriv_one]
  leibniz' a b := by
    change germDeriv v (stalkToModel f n p (a * b)) =
      a • germDeriv v (stalkToModel f n p b) + b • germDeriv v (stalkToModel f n p a)
    rw [map_mul, germDeriv_mul, stalkToModel_eval f n p a, stalkToModel_eval f n p b]
    rfl

/-- Literal original regular-function readback, PROVED for the actual
manufactured derivation rather than assumed as a certificate. -/
theorem nativeStalkDerivation_regular (E : ClosedProjectiveEmbedding f)
    (U : X.Opens) (r : Γ(X, U)) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) (v : ComplexModel n) :
    nativeStalkDerivation f n p v (X.presheaf.germ U (schemeComplexPointImage f p) hp r) =
      fderiv ℂ (schemeOpenRegularFunction f n E U r ∘ (complexChartAt (n := n) p).val.symm)
        ((complexChartAt (n := n) p).val p) v :=
  germDeriv_stalkToModel_germ f E n U r p hp v

/-- A genuine nonzero derivative of the actual original reader OUTPUTS
a genuine derivation nonzero on the SAME original algebraic germ. -/
theorem exists_nativeStalkDerivation_regular_ne_zero (E : ClosedProjectiveEmbedding f)
    (U : X.Opens) (r : Γ(X, U)) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U)
    (hD : fderiv ℂ
      (schemeOpenRegularFunction f n E U r ∘ (complexChartAt (n := n) p).val.symm)
        ((complexChartAt (n := n) p).val p) ≠ 0) :
    ∃ D : Derivation ℂ (X.presheaf.stalk (schemeComplexPointImage f p)) ℂ,
      D (X.presheaf.germ U (schemeComplexPointImage f p) hp r) ≠ 0 := by
  have hvec : ∃ v, fderiv ℂ
      (schemeOpenRegularFunction f n E U r ∘ (complexChartAt (n := n) p).val.symm)
        ((complexChartAt (n := n) p).val p) v ≠ 0 := by
    by_contra! hz
    apply hD
    ext v
    exact hz v
  obtain ⟨v, hv⟩ := hvec
  exact ⟨nativeStalkDerivation f n p v,
    (nativeStalkDerivation_regular f n E U r p hp v).symm ▸ hv⟩

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

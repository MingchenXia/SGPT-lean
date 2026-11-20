import SGPT.Okounkov.FlagValuationChowIdeals
import SGPT.GAGA.H0SSchemeEmbedding

/-!
# Original algebraic polynomial coefficients and native Chow functions

The existing `polyCoef` on the actual algebraic coordinate open is read
back as the literal normalized Chow polynomial function, first at points
and then as a WHOLE original native germ. Its actual global function-field
prefix value therefore detects the original analytic flag-member ideal.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov

open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance schemeChowTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance schemeChowCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance schemeChowManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- Exact values of the SAME original algebraic polynomial coefficient and
the actual normalized native Chow function, on the actual coordinate open. -/
theorem schemeOpenRegularFunction_polyCoef_eq_genFun
    (i : Fin (E.ambientDimension + 1)) (P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ)
    (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ coordOpen E i) :
    schemeOpenRegularFunction f n E (coordOpen E i) (polyCoef E i P) p =
      genFun (projectivePoint f E n) i P p := by
  rw [schemeOpenRegularFunction_polyCoef f n E i P p hp]
  change MvPolynomial.eval (homCoords f E n i p) P =
    MvPolynomial.eval (fun j => coneLift (projectivePoint f E n) i p j) P
  congr 1
  rw [homCoords_eq_affineLift f E n i hp]
  unfold coneLift
  rw [affineChart_projectivePoint f E n i hp]

/-- The WHOLE native germ, rather than merely the point value, of every
actual algebraic polynomial coefficient is the original Chow function. -/
theorem schemeNativeStalkGerm_polyCoef
    (i : Fin (E.ambientDimension + 1)) (P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ)
    (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ coordOpen E i) :
    letI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    schemeNativeStalkGerm f n p
        (X.presheaf.germ (coordOpen E i) (schemeComplexPointImage f p) hp (polyCoef E i P)) =
      NativeHolGerm.mk (genFun (projectivePoint f E n) i P)
        (holomorphicAt_genFun (isHolomorphicEmbedding_projectivePoint f E n)
          ((projectivePoint_mem_source_iff f E n i p).mpr hp) P) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  rw [← schemeOpenRegularFunction_germ f n E (coordOpen E i) (polyCoef E i P) p hp]
  apply NativeHolGerm.mk_eq_mk_iff.mpr
  filter_upwards [(isOpen_coordOpen_points f E i).mem_nhds hp] with q hq
  exact schemeOpenRegularFunction_polyCoef_eq_genFun f E n i P q hq

variable [IsIntegral X]

/-- The actual global function-field prefix of each original algebraic
Chow coefficient detects the original analytic flag-member ideal. -/
theorem schemeOriginalFlagPrefix_polyCoef_pos_iff
    (omega : KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
    (k : ℕ) (hk : k ≤ n) (i : Fin (E.ambientDimension + 1))
    (hi : schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n E omega Y hY).val ∈ coordOpen E i)
    (P : MvPolynomial (Fin (E.ambientDimension + 1)) ℂ) :
    (0 < ValCurr.prefixValuation hk (schemeOriginalFlagFunctionFieldValuation f n E omega Y hY)
      (algebraMap _ X.functionField
        (X.presheaf.germ (coordOpen E i)
          (schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n E omega Y hY).val)
          hi (polyCoef E i P))) ↔
      (vanishingIdeal (n := n) (Y ⟨k, Nat.lt_succ_of_le hk⟩)).mem
        (schemeProjectiveOriginalFlagPoint f n E omega Y hY).val
        (genFun (projectivePoint f E n) i P)) := by
  change 0 < ValCurr.prefixWithTopHom hk
    (schemeOriginalFlagFunctionFieldValuation f n E omega Y hY _) ↔ _
  rw [schemeOriginalFlagFunctionFieldValuation_stalk,
    schemeNativeStalkGerm_polyCoef f E n i P _ hi]
  exact originalFlagPrefixValuation_pos_iff_vanishingIdeal
    (schemeProjectiveOriginalFlagGeometry f n E omega Y hY)
    (schemeProjectiveOriginalFlagPoint f n E omega Y hY) k hk _ _

end SGPT.Okounkov

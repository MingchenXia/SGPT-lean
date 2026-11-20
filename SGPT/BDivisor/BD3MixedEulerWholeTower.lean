import SGPT.BDivisor.BD3MixedEulerCut
import SGPT.BDivisor.BD3MixedEulerCurveTerminal
import SGPT.BDivisor.BD3CITerminalDegreeTransport
import SGPT.Projective.OriginalCurveNativeGeometry
import Mathlib.Data.List.Forall2

/-! # Lane BD3: EP-free copy of `SGPT.Projective.OriginalMixedEulerWholeTower`

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749).  Proofs identical to the Codex module
`SGPT.Projective.OriginalMixedEulerWholeTower`; the only change is that the chain no longer imports
the earlier projective global-generation interface (replaced by
`SGPT.BDivisor.BD3ClopenGeneratedSection`), and every declaration carries the suffix `_bd3` so that
this copy can coexist with the original.

Original description: PURE original INTEGER mixed Euler differences along the SAME actual
whole algebraic CI, with genuine original global cutting powers.
Blueprint: original-mixed-euler-whole-tower.tex.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass

local instance wholeEulerTopology_bd3 {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance wholeEulerCharts_bd3 {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance wholeEulerManifold_bd3 {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

variable {X : Scheme.{0}}

/-- ONLY the actual original positive line's original power sheaf and atlas. -/
def originalPositivePowerLine_bd3 {f : X ⟶ Spec (.of ℂ)} {n : ℕ}
    [SmoothOfRelativeDimension n f] {E : ClosedProjectiveEmbedding f}
    (P : OriginalPositiveLine f n E) (q : ℕ) : IntrinsicLineBundle X where
  sheaf := bundleTensorPower P.sheaf q
  atlas := P.atlas.tensorPower q

/-- The ORIGINAL GLOBAL cutting powers, in the SAME actual tower order. -/
def originalCITowerCuttingDirections_bd3 (k : ℕ) {f : X ⟶ Spec (.of ℂ)}
    [SmoothOfRelativeDimension (k + 1) f] [IsSeparated f] [QuasiCompact f]
    {E : ClosedProjectiveEmbedding f} (P : Fin k → OriginalPositiveLine f (k + 1) E)
    (T : WholeOriginalCITower k f E P) : List (IntrinsicLineBundle X) :=
  List.ofFn (fun i => originalPositivePowerLine_bd3 (P i) (WholeOriginalCITower.powers k T i))

private theorem originalEuler_forall2_ofFn_bd3 (k : ℕ) {Y : Scheme.{0}}
    (As Cs : Fin k → IntrinsicLineBundle Y) (e : ∀ i, (As i).sheaf ≅ (Cs i).sheaf) :
    List.Forall₂ (fun A C => Nonempty (A.sheaf ≅ C.sheaf)) (List.ofFn As) (List.ofFn Cs) := by
  induction k with
  | zero => simp only [List.ofFn_zero]; exact .nil
  | succ k ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact .cons ⟨e 0⟩ (ih (fun i => As i.succ) (fun i => Cs i.succ) (fun i => e i.succ))

namespace WholeOriginalCITower

/-- PURE original whole-CI mixed Euler equals the INDEPENDENT original
terminal curve INTEGER degree. The actual original global cutting sheaves
are raised to the SAME actual powers. No regularity/exactness/Euler/period
comparison is supplied; arbitrary accumulated original testing line allowed. -/
theorem mixedEuler_eq_terminal_originalLineDegree_bd3 (k : ℕ) {Y : Scheme.{0}}
    (f : Y ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension (k + 1) f]
    [IsSeparated f] [QuasiCompact f] (E : ClosedProjectiveEmbedding f)
    (P : Fin k → OriginalPositiveLine f (k + 1) E) (T : WholeOriginalCITower k f E P)
    (A B : IntrinsicLineBundle Y) (p : Spec (.of ℂ)) :
    originalMixedEulerDifference f E (originalCITowerCuttingDirections_bd3 k P T ++ [A]) B =
      originalCurveLineDegree_bd3 (terminal k f T).structureMap ((terminal k f T).embedding E)
        (matePullbackAtlas (terminal k f T).inclusion A.atlas) p := by
  cases k with
  | zero =>
    erw [terminal.eq_1]
    dsimp only
    let C : OriginalCurveOver f :=
      { source := Y, structureMap := f, inclusion := 𝟙 Y, over_base := Category.id_comp f,
        closed := inferInstance, smooth := inferInstance }
    have hE : C.embedding E = E := originalCurveOver_identity_embedding_bd3 f E
    change originalMixedEulerDifference f E [A] B =
      originalCurveLineDegree_bd3 f (C.embedding E) (matePullbackAtlas (𝟙 Y) A.atlas) p
    rw [hE]
    exact (originalMixedEulerDifference_curve_singleton_bd3 f E A B p).trans
      (originalCurveLineDegree_eq_of_sheafIso_bd3 f E A.atlas (matePullbackAtlas (𝟙 Y) A.atlas)
        ((Scheme.Modules.pullbackId Y).app A.sheaf).symm p)
  | succ k =>
    erw [terminal.eq_1]
    dsimp only
    let C := T.1
    let Z := terminal k (C.inclusion ≫ f) T.2
    let R : OriginalCurveOver f :=
      { source := Z.source, structureMap := Z.structureMap, inclusion := Z.inclusion ≫ C.inclusion,
        over_base := by rw [Category.assoc, Z.over_base], closed := inferInstance, smooth := Z.smooth }
    let As : Fin k → IntrinsicLineBundle Y :=
      fun i => originalPositivePowerLine_bd3 (P i.succ) (powers k T.2 i)
    let Cs : Fin k → IntrinsicLineBundle C.scheme :=
      fun i => originalPositivePowerLine_bd3 (C.restrictLine (P i.succ)) (powers k T.2 i)
    let BZ := originalLinePullback C.inclusion (originalLineTensor B (originalCICutLine_bd3 f E (k + 1) (P 0) C))
    have hfirst := originalCICut_mixedEuler_restriction_bd3 f E (k + 1) (P 0) C
      (List.ofFn As ++ [A]) B
    have hlines : List.Forall₂ (fun U V => Nonempty (U.sheaf ≅ V.sheaf))
        ((List.ofFn As ++ [A]).map (originalLinePullback C.inclusion))
        (List.ofFn Cs ++ [originalLinePullback C.inclusion A]) := by
      simp only [List.map_append, List.map_ofFn, List.map_cons, List.map_nil]
      exact List.rel_append
        (originalEuler_forall2_ofFn_bd3 k (fun i => originalLinePullback C.inclusion (As i)) Cs
          (fun i => originalLinePullbackPowerIso C.inclusion (P i.succ).atlas (powers k T.2 i)))
        (.cons ⟨Iso.refl _⟩ .nil)
    have hcong := originalMixedEulerDifference_congr_lines_bd3 (C.inclusion ≫ f) C.embedding hlines BZ
    have htail := mixedEuler_eq_terminal_originalLineDegree_bd3 k (C.inclusion ≫ f) C.embedding
      (fun i => C.restrictLine (P i.succ)) T.2 (originalLinePullback C.inclusion A) BZ p
    have hiso := originalCurveLineDegree_eq_of_sheafIso_bd3 Z.structureMap (Z.embedding C.embedding)
      (matePullbackAtlas Z.inclusion (matePullbackAtlas C.inclusion A.atlas))
      (matePullbackAtlas (Z.inclusion ≫ C.inclusion) A.atlas)
      ((Scheme.Modules.pullbackComp Z.inclusion C.inclusion).app A.sheaf) p
    have hE : R.embedding E = Z.embedding C.embedding :=
      originalCurveOver_composite_embedding_bd3 f E ((P 0).atlas.tensorPower C.nativeCut.power)
        C.originalSection Z
    change _ = originalCurveLineDegree_bd3 Z.structureMap (R.embedding E)
      (matePullbackAtlas (Z.inclusion ≫ C.inclusion) A.atlas) p
    rw [hE]
    have h := hfirst.trans (hcong.trans (htail.trans hiso))
    simp only [originalCITowerCuttingDirections_bd3, List.ofFn_succ, powers, List.cons_append]
    change originalMixedEulerDifference f E
      (originalCICutLine_bd3 f E (k + 1) (P 0) C :: (List.ofFn As ++ [A])) B = _
    exact h
termination_by k

end WholeOriginalCITower
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

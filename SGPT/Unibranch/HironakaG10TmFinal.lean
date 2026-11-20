import SGPT.Unibranch.HironakaG10TmFlattenerCover
import SGPT.Unibranch.HironakaG10RdRoundMachine
import SGPT.Unibranch.HironakaG10TmTermination

/-!
# The terminal splice of Hironaka's flattening theorem (lane G10TM, G10-04-02 / G10-04-06)

`HironakaFlattening` (`HironakaG10ChowFlatteningReduction.HironakaFlattening`, the root target of G10) from
exactly two inputs:

* `hFrisch` — Frisch's two statements over every compact proper stage (`HironakaG10RdStratification`: Frisch
  1967 Th. (IV,9) + Remmert's proper mapping theorem, and Prop. (IV,14)); they give the finite flattener covers
  `hcover` (`HironakaG10TmFlattenerCover.hcover_of_frisch`, with Hironaka Th. 2.4 for closed non-compact `S`);
* `hI` — Theorem `I_n` with `B = X` (Hironaka p. 540; the input of
  `HironakaG10RdRoundMachine.nonempty_roundData_of_theoremI`).

The local input `PersistentLocalFlattener` is PROVED (lane G10MW, `HironakaG10MwNativeWindow.persistentLocalFlattener`)
and gives the closed non-flat images of every run (G10-04-02: `machine_hclosed_actual`).  No named `Prop`.
-/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace SGPT.Unibranch.HironakaG10TmFinal

open SGPT.Unibranch
open SGPT.Unibranch.SourceReducedComplexSpace
  SGPT.Unibranch.HironakaG10ChowFlatteningDriver SGPT.Unibranch.HironakaG10ChowCentreMachine
  SGPT.Unibranch.HironakaG10ChowStrictTransformCalculus SGPT.Unibranch.HironakaG10ChowFlatteningReduction
  SGPT.Unibranch.HironakaG10RelativeNonflatStrata SGPT.Unibranch.HironakaG10SourceCSet
  SGPT.Unibranch.HironakaG10RdPermRun SGPT.Unibranch.HironakaG10RdRoundMachine
  SGPT.Unibranch.HironakaG10HirLocalFlattener SGPT.Unibranch.HironakaG10MwNativeWindow
  SGPT.Unibranch.HironakaG10TmFlattenerCover SGPT.Unibranch.HironakaG10TmTermination

noncomputable section

/-- **G10-04-02: closed non-flat images along every run of every centre machine**, unconditionally. -/
theorem machine_hclosed_actual (M : CentreMachine) (s₀ : Stage) (d₀ : M.St s₀)
    (hf : IsProperMap s₀.f.hom.left.base) (n : ℕ) :
    IsClosed ((toFlatteningSequence M s₀ d₀ hf).nonflatImage n) :=
  machine_hclosed persistentLocalFlattener M s₀ d₀ hf n

/-- **G10-04-06 (conditional on Frisch's stratification and Theorem `I_n`): `HironakaFlattening`.** -/
theorem hironakaFlattening_of_frisch_of_theoremI
    (hFrisch : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      (∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → s.X.IsAnalyticSubset (relNonflat s.f A)) ∧
      (∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat s.f A)))
    (hI : ∀ (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → R.B = univ →
        ∃ l : PermRun s R, ∀ p, IsRelOpen l.final.2.B (l.final.2.Z p).support) :
    HironakaFlattening :=
  hironakaFlattening_of_roundData persistentLocalFlattener fun s₀ hX hf =>
    nonempty_roundData_of_theoremI s₀ hX hf (hcover_of_frisch hFrisch) hI

end

end SGPT.Unibranch.HironakaG10TmFinal

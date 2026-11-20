import SGPT.Okounkov.TranscendentalExtensionTheorem
import SGPT.Okounkov.TranscendentalExtensionGentle
import SGPT.Okounkov.TranscendentalPoleExtension

/-!
# Extension of Kähler currents from a submanifold: the theorems

Package EXT, blueprint nodes `tok:ct-extension`, `tok:ct-gentle`. The pole input
`NormalPoleStatement` (blueprint `tok:ext-pole`) is discharged by package POLE
(`SGPT.Okounkov.TranscendentalPole.normalPoleStatement`), so the conditional results of
`TranscendentalExtensionTheorem` become unconditional:

* `kahlerCurrentExtensionStatement`: **the book's `thm:CT-thm-refined'`** (chapter
  *Quasi-plurisubharmonic functions*): for a connected compact Kähler manifold `(X, ω)`, a
  connected closed submanifold `Y` of any dimension and `φ ∈ PSH(Y, ω|_Y)` with `ω|_Y + dd^c φ`
  a Kähler current and `e^φ` Hölder continuous, there is `φ̃ ∈ PSH(X, ω)` with `φ̃|_Y = φ` and
  `ω + dd^c φ̃` a Kähler current; if `φ` has analytic singularities, so does `φ̃`;
* `continuousKahlerCurrentExtensionStatement`: DRWNXZ Theorem 6.1 in the form of
  `tok:ct-extension` (moreover `φ̃` is finite and continuous on `X \ Y`);
* `gentleExtensionStatement`: DRWNXZ Theorem 6.4 (`tok:ct-gentle`): a Kähler current with gentle
  analytic singularities on `Y` extends to a Kähler current on `X` with analytic singularities,
  restricting to the given potential and finite and continuous off `Y`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalExtension

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **Source `thm:CT-thm-refined'`** for fixed data. -/
theorem hasKahlerCurrentExtension [CompactSpace X] [ConnectedSpace X] (ω : KahlerBackground n X)
    {Y : Set X} {k : ℕ} (hY : IsClosedConnectedSubmanifold n Y k) :
    HasKahlerCurrentExtension ω hY :=
  hasKahlerCurrentExtension_of_normalPoleStatement TranscendentalPole.normalPoleStatement ω hY

/-- **DRWNXZ Theorem 6.1** (`tok:ct-extension`) for fixed data. -/
theorem hasContinuousKahlerCurrentExtension [CompactSpace X] [ConnectedSpace X]
    (ω : KahlerBackground n X) {Y : Set X} {k : ℕ} (hY : IsClosedConnectedSubmanifold n Y k) :
    HasContinuousKahlerCurrentExtension ω hY :=
  hasContinuousKahlerCurrentExtension_of_normalPoleStatement
    TranscendentalPole.normalPoleStatement ω hY

/-- **Source `thm:CT-thm-refined'`** (book, chapter *Quasi-plurisubharmonic functions*). -/
theorem kahlerCurrentExtensionStatement : KahlerCurrentExtensionStatement.{u} :=
  kahlerCurrentExtensionStatement_of_normalPoleStatement TranscendentalPole.normalPoleStatement

/-- **DRWNXZ Theorem 6.1** (blueprint `tok:ct-extension`). -/
theorem continuousKahlerCurrentExtensionStatement :
    ContinuousKahlerCurrentExtensionStatement.{u} :=
  continuousKahlerCurrentExtensionStatement_of_normalPoleStatement
    TranscendentalPole.normalPoleStatement

/-- **DRWNXZ Theorem 6.4** (blueprint `tok:ct-gentle`) for fixed data; it holds for every
dimension of `Y`. -/
theorem hasGentleKahlerCurrentExtension [CompactSpace X] [ConnectedSpace X]
    (κ : KahlerBackground n X) {Y : Set X} {k : ℕ} (hY : IsClosedConnectedSubmanifold n Y k) :
    HasGentleKahlerCurrentExtension κ hY := by
  let _ := submanifoldCharts hY
  have _ := submanifold_isComplexManifold hY
  intro φ hKah hgentle
  obtain ⟨c, 𝔞, hg⟩ := hgentle
  have hHol := isChartHolder_expPotential_of_gentle hg
  have han : HasManifoldAnalyticSingularityType (n := k) φ :=
    TranscendentalPole.hasManifoldAnalyticSingularityType_of_hasAnalyticSingularitiesOfType
      hg.2.2.1
  obtain ⟨φ', ε, hε, hpsh, hres, hcont, hne, hanφ⟩ :=
    exists_extension TranscendentalPole.normalPoleStatement κ hY φ hKah hHol
  exact ⟨φ', isKahlerCurrentPotential_of_one_sub κ hε hpsh, hanφ han, hres, hcont, hne⟩

/-- **DRWNXZ Theorem 6.4** (blueprint `tok:ct-gentle`). -/
theorem gentleExtensionStatement : GentleExtensionStatement.{u} := by
  intro n X _ _ _ _ _ κ Y k hY _ _
  exact hasGentleKahlerCurrentExtension κ hY

end SGPT.Okounkov.TranscendentalExtension

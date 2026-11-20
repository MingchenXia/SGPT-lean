import SGPT.Unibranch.FNHGeneral
import SGPT.Unibranch.FNPChart

/-!
# The Fornæss–Narasimhan theorem `thm:FN` (lane FNH, final assembly)

Source `thm:FN` (`appendix_unibranch.tex`), citing Fornæss–Narasimhan, *The Levi problem on
complex spaces with singularities*, Math. Ann. 248 (1980), Theorem 5.3.1 (`[FN80]`): for a
function `φ : X → [-∞, ∞)` on a complex space `X`, not identically `-∞` on any irreducible
component of `X`, the following are equivalent:

1. `φ` is plurisubharmonic (`def:unibranch:L105`);
2. `φ` is upper semicontinuous and, for every morphism `f : Δ → X` from the open unit disc with
   `f^*φ ≢ -∞`, the pull-back `f^*φ` is subharmonic.

All inputs are now theorems: the local parametrization theorem `FNP.localCoveringCharts`
, the Runge half of `[FN80, Thm. 5.3.1]` (`FNH.hartogsRungeOfEquations_of_charts`,
from `[FN80]` Lemma 5.2 `FNL.runge_sublevel`, Rossi's local maximum principle
`FNR.mem_polyHull_inter_sphere` and the suspension), the Siu/Hartogs half
(`FNS.exists_ambient_psh_of_hartogsRunge`, packaged as `FNS.localFNExtension_of_hartogsRunge`),
and the bridge to complex spaces (`FNA.fornaessNarasimhan`).

* `hartogsRunge`: `[FN80, Thm. 5.3.1]` first half for every closed analytic subset of a polydisc;
* `hartogsRungeOfEquations : FNS.HartogsRungeOfEquations`;
* `localFNExtension : FNA.LocalFNExtension` (the local `[FN80, Thm. 5.3.1]`);
* `isPSH_of_disc`: `thm:FN`, (2) ⇒ (1);
* `fornaessNarasimhan`: **`thm:FN`**, (1) ⇔ (2), on every complex space.
-/

set_option autoImplicit false

open Set Metric CategoryTheory
open SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.FNH

open SourceReducedComplexSpace

/-- **`[FN80, Thm. 5.3.1]`, first half.** For `X` closed analytic in an open polydisc `Δ(a, r)`
and `φ ∈ WP(X)`, the Hartogs domain `{(w, z) : z ∈ X, φ(z) + log |w| < 0}` is Runge in `X × ℂ`. -/
theorem hartogsRunge {n : ℕ} {X : Set (ComplexModel n)} {a : ComplexModel n} {r : Fin n → ℝ}
    (hXΔ : X ⊆ FNA.polydisc a r) (hloc : FNR.HasLocalEquationsOn X (FNA.polydisc a r))
    {φ : ComplexModel n → EReal} (hφ : FNL.IsWeaklyPSHOn X φ) : FNS.HartogsRunge X φ :=
  hartogsRunge_of_hasLocalEquationsOn FNP.localCoveringCharts hXΔ hloc hφ

/-- the interface `HartogsRungeOfEquations` holds. -/
theorem hartogsRungeOfEquations : FNS.HartogsRungeOfEquations :=
  hartogsRungeOfEquations_of_charts FNP.localCoveringCharts

/-- **The local `[FN80, Thm. 5.3.1]`**: for `X` closed analytic in an open polydisc centred at
`a ∈ X` and `φ ∈ WP(X)`, near `a` the function `φ` is the restriction of an ambient function
satisfying the disc criterion. -/
theorem localFNExtension : FNA.LocalFNExtension :=
  FNS.localFNExtension_of_hartogsRunge hartogsRungeOfEquations

/-- **Source `thm:FN`, (2) ⇒ (1)**, on every complex space. -/
theorem isPSH_of_disc {X : SourceReducedComplexSpace} {φ : X.obj.left → EReal}
    (hne_top : ∀ x, φ x ≠ ⊤)
    (hcomp : ∀ Z : Set X.obj.left, X.IsIrreducibleComponent Z → ∃ z ∈ Z, φ z ≠ ⊥)
    (husc : UpperSemicontinuous φ)
    (hdisc : ∀ f : unitDisc ⟶ X, (∃ t ∈ ball (0 : ℂ) 1, discPullback f φ t ≠ ⊥) →
      SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1)) :
    X.IsPSH φ :=
  FNA.isPSH_of_disc localFNExtension hne_top hcomp husc hdisc

/-- **Source `thm:FN` (Fornæss–Narasimhan).** Let `X` be a complex space and
`φ : X → [-∞, ∞)` not identically `-∞` on any irreducible component of `X`. Then `φ` is
plurisubharmonic if and only if `φ` is upper semicontinuous and, for every morphism `f : Δ → X`
from the open unit disc with `f^*φ ≢ -∞`, the pull-back `f^*φ` is subharmonic. -/
theorem fornaessNarasimhan {X : SourceReducedComplexSpace} {φ : X.obj.left → EReal}
    (hne_top : ∀ x, φ x ≠ ⊤)
    (hcomp : ∀ Z : Set X.obj.left, X.IsIrreducibleComponent Z → ∃ z ∈ Z, φ z ≠ ⊥) :
    X.IsPSH φ ↔
      (UpperSemicontinuous φ ∧
        ∀ f : unitDisc ⟶ X, (∃ t ∈ ball (0 : ℂ) 1, discPullback f φ t ≠ ⊥) →
          SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1)) :=
  FNA.fornaessNarasimhan localFNExtension hne_top hcomp

end SGPT.Unibranch.FNH

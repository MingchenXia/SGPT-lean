import SGPT.Okounkov.TranscendentalWNConvFL4Exc
import SGPT.Okounkov.TranscendentalWNConvFL4Lipschitz
import SGPT.Okounkov.TranscendentalWNConvFL4Disc
import SGPT.Okounkov.TranscendentalWNConvFLMain
import SGPT.Okounkov.TranscendentalMainAssembly

/-!
# WN21 Proposition 7.4 near `ℰ \ X'`, unconditionally

Blueprint `claude-tok-wn-fl4`, node `tok-wn-fl4:exceptional-convergence`
(= `tok-wn-fl:exceptional-convergence`); source WN21 §7 (`references/wn21-restricted-volume`).

* `excLipschitz : ExcLipschitzStatement F` (WN21 Corollary 7.6 along fibre discs), from
  `excDiscLaplacian` (WN21 Lemma 7.5 along fibre discs) and `excLipschitz_of_excDiscLaplacian`;
* **`exceptionalFibreConvergence : ExceptionalFibreConvergenceStatement F`** (WN21
  Proposition 7.4 near `ℰ \ X'`, upper-bound form), from `exceptionalFibreConvergence_of_excLipschitz`.

With the reduction and the strict side this closes the fibre limit
(`fibreLimit_of_FL4 : FibreLimitStatement F`, via WN-FL's
`fibreLimit_of_strictDiscLaplacianFrom_of_exceptional` and WN-FL5's `strictDiscLaplacianFrom`) and
hence the corrected `thm:Okounkovtranmain` (`okounkovTranMain_of_FL4`, via
`okounkovTranMain_of_fibreLimit`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open SGPT.Okounkov.TranscendentalMain

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **`tok-wn-fl4:lipschitz`** (WN21 Corollary 7.6 along holomorphic families of fibre discs). -/
theorem excLipschitz : ExcLipschitzStatement F :=
  excLipschitz_of_excDiscLaplacian F (excDiscLaplacian F)

/-- **`tok-wn-fl4:exceptional-convergence`** (WN21 Proposition 7.4 near `ℰ \ X'`, as an upper
bound): `ExceptionalFibreConvergenceStatement F` holds. -/
theorem exceptionalFibreConvergence : ExceptionalFibreConvergenceStatement F :=
  exceptionalFibreConvergence_of_excLipschitz F (excLipschitz F)

/-- **`tok-wn-conv7:fibre-limit`**: `FibreLimitStatement F` holds (WN-FL's reduction, WN-FL2's
smallness estimate, WN-FL5's Lemma 7.5 near `X' \ ℰ`, and `exceptionalFibreConvergence`). -/
theorem fibreLimit_of_FL4 : FibreLimitStatement F :=
  fibreLimit_of_strictDiscLaplacianFrom_of_exceptional F (strictDiscLaplacianFrom F)
    (exceptionalFibreConvergence F)

end SGPT.Okounkov.TranscendentalWN

namespace SGPT.Okounkov.TranscendentalMain

/-- **`thm:Okounkovtranmain`** (corrected: item 5 for Kähler classes), unconditionally:
`okounkovTranMain_of_fibreLimit` with `fibreLimit_of_FL4`. -/
theorem okounkovTranMain_of_FL4 :
    ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 1)), OkounkovTranMainStatement F :=
  okounkovTranMain_of_fibreLimit fun _ F => SGPT.Okounkov.TranscendentalWN.fibreLimit_of_FL4 F

end SGPT.Okounkov.TranscendentalMain

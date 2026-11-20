import SGPT.Okounkov.TranscendentalWNConvFLStrict
import SGPT.Okounkov.TranscendentalWNConvFLLipschitz
import SGPT.Okounkov.TranscendentalWNConvFL2
import SGPT.Okounkov.TranscendentalWNConvFL3Disc

/-!
# The fibre limit of WN21 §7: assembly

Blueprint `claude-tok-wn-fl`, node `tok-wn-fl:assembly`; refines `tok-wn-conv7:fibre-limit`.

`FibreLimitStatement F` from Lemma 7.5 along the discs near `X' \ ℰ`
(`StrictDiscLaplacianStatement F`, equal to WN-FL3's `StrictDiscLaplacianFromStatement F`) and the
exceptional side of Proposition 7.4 (`ExceptionalFibreConvergenceStatement F`):

* `strictFibreConvergence_of_strictDiscLaplacian`: Corollary 7.6
  (`strictLipschitz_of_strictDiscLaplacian`) and Proposition 7.4 near `X' \ ℰ`
  (`strictFibreConvergence_of_strictLipschitz`);
* `fibreLimit_of_strictDiscLaplacian_of_exceptional`: with the smallness estimate (eqeq) of
  WN-FL2 (`fibreVolumeSmall`) and the reduction `fibreLimit_of_fibreVolumeSmall_of_local`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- The two published forms of the corrected WN21 Lemma 7.5 coincide. -/
theorem strictDiscLaplacian_of_strictDiscLaplacianFrom (h : StrictDiscLaplacianFromStatement F) :
    StrictDiscLaplacianStatement F := h

/-- **WN21 Proposition 7.4 near `X' \ ℰ`** from Lemma 7.5 along the discs. -/
theorem strictFibreConvergence_of_strictDiscLaplacian (hD : StrictDiscLaplacianStatement F) :
    StrictFibreConvergenceStatement F :=
  strictFibreConvergence_of_strictLipschitz F (strictLipschitz_of_strictDiscLaplacian F hD)

/-- **`tok-wn-conv7:fibre-limit`** from Lemma 7.5 along the discs near `X' \ ℰ` and the
exceptional side of Proposition 7.4 (the smallness estimate is WN-FL2's `fibreVolumeSmall`). -/
theorem fibreLimit_of_strictDiscLaplacian_of_exceptional (hD : StrictDiscLaplacianStatement F)
    (hX : ExceptionalFibreConvergenceStatement F) : FibreLimitStatement F :=
  fibreLimit_of_fibreVolumeSmall_of_local F (fibreVolumeSmall F)
    (strictFibreConvergence_of_strictDiscLaplacian F hD) hX

/-- The same with WN-FL3's form of Lemma 7.5. -/
theorem fibreLimit_of_strictDiscLaplacianFrom_of_exceptional
    (hD : StrictDiscLaplacianFromStatement F) (hX : ExceptionalFibreConvergenceStatement F) :
    FibreLimitStatement F :=
  fibreLimit_of_strictDiscLaplacian_of_exceptional F
    (strictDiscLaplacian_of_strictDiscLaplacianFrom F hD) hX

end SGPT.Okounkov.TranscendentalWN

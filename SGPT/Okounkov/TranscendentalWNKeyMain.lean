import SGPT.Okounkov.TranscendentalWNKeyEasy
import SGPT.Okounkov.TranscendentalWNVolumeFibre

/-!
# Witt Nyström's Theorem C: the conditional assembly (packages WN-KEY and WN-ASM)

Blueprint chapter `claude-tok-wn` (nodes `tok-wn:integrated`, `tok-wn:derivative`) and
`claude-tok-wn-key` (node `tok-wn-key:main`).  Combining

* the reduction of the key easy inequality to the lower semicontinuity of fibre masses
  (`keyEasy_of_fibreMassLSC`, this package),
* the key equality from its two halves (`keyEquality_of_keyEasy_of_keyConvergence`),
* the integrated formula from the key equality (`wnIntegrated_of_keyEquality`) and the
  derivative from the integrated formula (`wnDerivative_of_wnIntegrated`),
* the restricted volumes along the fibres and along `X'` (`restrictedVolume_fibre`,
  `restrictedVolume_strictTransform`, package WN-VF, proved from `BetaBigStatement`),

WN21 Theorem C (in the integrated form with continuity, `WNStatement`, consumed by package VOL,
and in the derivative form `WNDerivativeStatement`, `tok:ext-wn21`) holds **conditionally** on
exactly four named statements:

* `FibreMassLSCStatement` (WN-KEY, `tok-wn-key:fibre-mass-lsc`, WN21 §5; open),
* `KeyConvergenceStatement` (WN-KEY, `tok-wn:convergence`, WN21 §§6--7; open),
* `BetaBigStatement` (WN-DEF, `tok-wn:beta-big`, WN21 Proposition 4.1; open, lane WN-DEF2),
* `ExceptionalRestrictedVolumeStatement` (WN-VF, `tok-wn:formula-E`, WN21 Theorem 1.6 (4);
  open, lane WN-VF3).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open SGPT.Okounkov.TranscendentalMain

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **`tok-wn:key-easy`**, conditional on the analytic core `FibreMassLSCStatement` and on
`tok-wn:beta-big` (the fibre formula `tok-wn:formula-fibre` is `restrictedVolume_fibre`). -/
theorem keyEasy_of_fibreMassLSC_of_betaBig (hL : FibreMassLSCStatement F)
    (hBeta : BetaBigStatement F) : KeyEasyStatement F :=
  keyEasy_of_fibreMassLSC F hL (restrictedVolume_fibre F hBeta) hBeta

/-- **`tok-wn:key-equality`** (WN21 Theorem 1.7), conditional on `FibreMassLSCStatement`,
`KeyConvergenceStatement` and `BetaBigStatement`. -/
theorem keyEquality_of_wnKey (hL : FibreMassLSCStatement F) (hConv : KeyConvergenceStatement F)
    (hBeta : BetaBigStatement F) : KeyEqualityStatement F :=
  keyEquality_of_keyEasy_of_keyConvergence F (keyEasy_of_fibreMassLSC_of_betaBig F hL hBeta)
    hConv hBeta

/-- **`tok-wn:integrated`** (WN21 Theorems 1.6--1.7; DRWNXZ proof of Theorem 2.10):
`vol(ξ) - vol(ξ_c) = n ∫₀^c vol_{X|Y₁}(ξ_t) dt`, conditional on `FibreMassLSCStatement`,
`KeyConvergenceStatement`, `BetaBigStatement` and `ExceptionalRestrictedVolumeStatement`. -/
theorem wnIntegrated_of_wnKey (hL : FibreMassLSCStatement F) (hConv : KeyConvergenceStatement F)
    (hBeta : BetaBigStatement F) (hEx : ExceptionalRestrictedVolumeStatement F) :
    WNIntegratedStatement F :=
  wnIntegrated_of_keyEquality F (keyEquality_of_wnKey F hL hConv hBeta)
    (restrictedVolume_strictTransform F hBeta) hEx

/-- **WN21 Theorem C, integrated form with continuity** (`WNStatement`, consumed by package
VOL), conditional on the same four named statements as `wnIntegrated_of_wnKey`. -/
theorem wnStatement_of_wnKey (hL : FibreMassLSCStatement F) (hConv : KeyConvergenceStatement F)
    (hBeta : BetaBigStatement F) (hEx : ExceptionalRestrictedVolumeStatement F) :
    WNStatement F :=
  ⟨wnIntegrated_of_wnKey F hL hConv hBeta hEx, wnContinuity F⟩

/-- **WN21 Theorem C** (`tok:ext-wn21`, DRWNXZ Theorem 2.10, first point), conditional on the
same four named statements. -/
theorem wnDerivative_of_wnKey (hL : FibreMassLSCStatement F) (hConv : KeyConvergenceStatement F)
    (hBeta : BetaBigStatement F) (hEx : ExceptionalRestrictedVolumeStatement F) :
    WNDerivativeStatement F :=
  wnDerivative_of_wnIntegrated F (wnIntegrated_of_wnKey F hL hConv hBeta hEx)

end SGPT.Okounkov.TranscendentalWN

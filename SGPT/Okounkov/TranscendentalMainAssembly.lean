import SGPT.Okounkov.TranscendentalCoreRepresentative
import SGPT.Okounkov.TranscendentalBodyBasic
import SGPT.Okounkov.TranscendentalBodyConvex
import SGPT.Okounkov.TranscendentalBodyHausdorff
import SGPT.Okounkov.TranscendentalSlice
import SGPT.Okounkov.TranscendentalL2Corollaries
import SGPT.Okounkov.TranscendentalVolIdPointDegree
import SGPT.Okounkov.TranscendentalWNKeyLSC
import SGPT.Okounkov.TranscendentalWNConvPW
import SGPT.Okounkov.TranscendentalWNConv6Main
import SGPT.Okounkov.TranscendentalWNVolumeExcMain
import SGPT.Okounkov.TranscendentalWNVolumeGlobalExcInput
import SGPT.Okounkov.TranscendentalWNVolumeBundleAssembly

/-!
# Assembly of `thm:Okounkovtranmain` (corrected statement)

`okounkovTranMain_of_wnInputs`: the full `TranscendentalMain.OkounkovTranMainStatement` for every
flag geometry, from the two statements of the WN package (WN21 Theorem C) that are still open,
`FibreLimitStatement` (WN21 §7) and `ExcBundleLegendreMAStatement` (WN21 Thm 3.5 on the
exceptional `ℂ*`-bundle), required for flag geometries of dimension `≥ 2`. Every other input is
proved: representative independence and the convex-body clause (CORE, BODY), items 2, 4 (BODY),
item 3 (L² relative global generation), item 5 for Kähler classes (SLICE; the printed item 5 is
false, ERRATA E12), the induction for item 1 (VOL, dimension one unconditional), and of WN21
Theorem C: Prop 4.1, Thm 3.3, Thm 1.6 (1), §5, §6 and the perturbed-weight step of §7.
-/

namespace SGPT.Okounkov.TranscendentalMain

open SGPT.Okounkov.TranscendentalWN

universe u

/-- WN21 Theorem C (`WNStatement`) from the two open WN inputs. -/
theorem wnStatement_of_wnInputs {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (hFL : FibreLimitStatement F) (hEx : ExcBundleLegendreMAStatement F) : WNStatement F :=
  wnStatement_of_keyConvergence F
    (keyConvergence_of_measureControl_of_fibreLimit F (measureControl F) hFL)
    (exceptionalRestrictedVolume_of_bundleLegendre F (excLegendreInput F) hEx)

/-- **`thm:Okounkovtranmain`** (corrected: item 5 for Kähler classes), conditional only on the
two open statements of WN21 Theorem C in dimensions `≥ 2`. -/
theorem okounkovTranMain_of_wnInputs
    (hFL : ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 2)), FibreLimitStatement F)
    (hEx : ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 2)), ExcBundleLegendreMAStatement F) :
    ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 1)), OkounkovTranMainStatement F := by
  intro m F
  have hVol : ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 1)), VolumeIdentityStatement F :=
    TranscendentalVolId.volumeIdentityStatement_of_wn fun m F =>
      wnStatement_of_wnInputs F (hFL m F) (hEx m F)
  exact ⟨TranscendentalCore.representativeIndependence F, TranscendentalBody.isConvexBody F,
    hVol m F, TranscendentalBody.superadditivity F, TranscendentalL2.liftingInvarianceStatement F,
    TranscendentalBody.hausdorffContinuity F, TranscendentalSlice.kahlerSliceFormula F⟩

/-- **`thm:Okounkovtranmain`** (corrected: item 5 for Kähler classes), conditional only on
`FibreLimitStatement` (WN21 §7) in dimensions `≥ 2`; the exceptional-divisor formula is proved
(`exceptionalRestrictedVolume_formula`, via `excBundleLegendreMA`). -/
theorem okounkovTranMain_of_fibreLimit
    (hFL : ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 2)), FibreLimitStatement F) :
    ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 1)), OkounkovTranMainStatement F :=
  okounkovTranMain_of_wnInputs hFL fun _ F => excBundleLegendreMA F

end SGPT.Okounkov.TranscendentalMain

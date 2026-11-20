import SGPT.Okounkov.TranscendentalWNRestricted
import SGPT.Okounkov.TranscendentalWNCone2
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction

/-!
# Continuity of the restricted volume along `Y₁`: `WNContinuityStatement`

Blueprint node `tok-wn:continuity` (chapter `claude-tok-wn`; Matsumura 2013, Corollary 4.11,
cited by DRWNXZ §2; Collins--Tosatti, Corollary 5.3, here for the DRWNXZ restricted volume):
if `ξ` and `ξ - c{Y₁}` are big with Kähler loci meeting `Y₁`, then
`t ↦ vol_{X|Y₁}(ξ - t{Y₁})` is continuous on `[0, c]`.

Proof: by the convexity of the cone `𝒜_{Y₁}` (`isBigMeetingFirstDivisor_sub_smul_of_mem_Icc`)
every `ξ_{t₀} = ξ - t₀{Y₁}`, `t₀ ∈ [0, c]`, lies in `𝒜_{Y₁}`, and `ξ - t{Y₁} = ξ_{t₀} + (t₀ - t){Y₁}`;
the continuity of `s ↦ vol_{X|Y₁}(ξ_{t₀} + s{Y₁})` at `s = 0`
(`continuousAt_classRestrictedVolume_add_smul`, from the two-sided perturbation bounds) gives the
continuity at `t₀`.

## Main results

* `isKahler_pullback_firstFlagInclusion`: `ω|_{Y₁}` is Kähler;
* `continuousAt_firstFlagRestrictedVolume_add_smul`: continuity of `s ↦ vol_{X|Y₁}(ξ + s{γ})` at
  `0` for `ξ ∈ 𝒜_{Y₁}` (`tok-wn:restricted-perturbation` along `Y₁`);
* `wnContinuity`: **`WNContinuityStatement F`** (`tok-wn:continuity`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- The pullback of the Kähler form of `X` to `Y₁` is Kähler. -/
theorem isKahler_pullback_firstFlagInclusion :
    (ClosedRealOneOneForm.pullback (contMDiff_firstFlagInclusion F) F.omega.form).val.IsKahler :=
  SubmanifoldKahlerRestriction.isKahler_pullback (Nat.le_succ m) F.firstDivisor.2.2
    F.omega.form F.omega.isKahler

/-- **`tok-wn:restricted-perturbation` along `Y₁`**: for `ξ ∈ 𝒜_{Y₁}` and a closed real smooth
`(1,1)`-form `γ`, `s ↦ vol_{X|Y₁}(ξ + s{γ})` is continuous at `s = 0`. -/
theorem continuousAt_firstFlagRestrictedVolume_add_smul {ξ : RealBottChern (m + 1) F.carrier}
    (hξ : IsBigMeetingFirstDivisor F ξ) (γ : ClosedRealOneOneForm (m + 1) F.carrier) :
    ContinuousAt (fun s : ℝ => (firstFlagRestrictedVolume F
      (ξ + s • RealBottChern.ofRepresentative γ)).toReal) 0 := by
  obtain ⟨hbig, hZ⟩ := (isBigMeetingFirstDivisor_iff F ξ).mp hξ
  let : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  have : BorelSpace F.tail.carrier := ⟨rfl⟩
  exact continuousAt_classRestrictedVolume_add_smul (contMDiff_firstFlagInclusion F) F.omega
    (isKahler_pullback_firstFlagInclusion F) ξ γ hbig hZ

/-- **`tok-wn:continuity`** (Matsumura 2013, Corollary 4.11; Collins--Tosatti, Corollary 5.3, for
the DRWNXZ restricted volume): if `ξ` and `ξ - c{Y₁}` (`c ≥ 0`) are big with Kähler loci meeting
`Y₁`, then `t ↦ vol_{X|Y₁}(ξ - t{Y₁})` is continuous on `[0, c]`. -/
theorem wnContinuity : WNContinuityStatement F := by
  intro ξ E _hE c _hc hξ hξc t₀ ht₀
  set e := RealBottChern.ofRepresentative E.curvature with he
  have hA := isBigMeetingFirstDivisor_sub_smul_of_mem_Icc F hξ hξc ht₀
  have hg := continuousAt_firstFlagRestrictedVolume_add_smul F hA E.curvature
  have hfun : (fun t : ℝ => (firstFlagRestrictedVolume F (ξ - t • e)).toReal) =
      (fun s : ℝ => (firstFlagRestrictedVolume F ((ξ - t₀ • e) + s • e)).toReal) ∘
        (fun t : ℝ => t₀ - t) := by
    funext t
    simp only [Function.comp]
    congr 2
    module
  refine ContinuousAt.continuousWithinAt ?_
  rw [hfun]
  exact ContinuousAt.comp_of_eq hg (continuous_const.sub continuous_id).continuousAt (by simp)

end SGPT.Okounkov.TranscendentalWN

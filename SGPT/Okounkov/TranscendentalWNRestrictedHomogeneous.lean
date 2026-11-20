import SGPT.Okounkov.TranscendentalWNRestricted
import SGPT.Okounkov.TranscendentalWNCone2
import SGPT.Foundations.Analysis.Pending.ActualPositiveClassScaling

/-!
# Homogeneity of the restricted volume

Blueprint node `tok-wn:restricted-homogeneous` (chapter `claude-tok-wn`; Collins--Tosatti,
Section 2, homogeneity of the restricted volume): for `ξ ∈ 𝒜_Z` and `λ > 0`, `λξ ∈ 𝒜_Z` and
`vol_{X|Z}(λξ) = λ^d vol_{X|Z}(ξ)`, `d = dim Z`.

Proof: `E_nK(λξ) ∌` the points where a Kähler current of `ξ` with polar set `E_nK(ξ)` is finite
(`isBigClass_meeting_smul`). By the identification
`vol_{X|Z}(ξ) = ∫_Z ⟨(θ|_Z + dd^c V_θ|_Z)^d⟩` (`restrictedVolume_eq_restrictedMinimalMass`),
`V_{λθ} = λV_θ` (TN `ActualPositiveClassScaling.thetaPshSupremum_positive_smul`) and the
homogeneity of non-pluripolar masses (TN `RestrictedApproximantComparison.diagonalPotentialMass_smul`).

## Main results

* `restrictedVolume_smul`, `classRestrictedVolume_smul`: `R(λξ) = λ^d R(ξ)`;
* `firstFlagRestrictedVolume_smul`: the case `Z = Y₁` (`d = n - 1`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set
open scoped ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass

section Homogeneity

open TranscendentalVolumeConcavity

variable {m k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ConnectedSpace X]
  {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
  {ι : V → X} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel (m + 1)) ∞ ι)

include hι in
/-- **`tok-wn:restricted-homogeneous`**: if `{θ}` is big with Kähler locus meeting `ι(V)` and
`c > 0`, then `R(cθ) = c^k R(θ)`. -/
theorem restrictedVolume_smul (w : KahlerBackground (m + 1) X)
    (hpull : (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)
    (θ : ClosedRealOneOneForm (m + 1) X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hZ : ∃ y : V, ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ))
    {c : ℝ} (hc : 0 < c) :
    restrictedVolume ι hι (c • θ) = ENNReal.ofReal (c ^ k) * restrictedVolume ι hι θ := by
  obtain ⟨hV, hR⟩ := restrictedVolume_eq_restrictedMinimalMass hι w hpull θ hbig hZ
  obtain ⟨hbigc, hZc⟩ := isBigClass_meeting_smul hι (Nat.succ_pos m) hbig hZ hc
  obtain ⟨hVc, hRc⟩ := restrictedVolume_eq_restrictedMinimalMass hι w hpull (c • θ) hbigc hZc
  have hscale := ActualPositiveClassScaling.thetaPshSupremum_positive_smul w θ hbig hc
  have hcu : IsThetaPshPotential (c • ClosedRealOneOneForm.pullback hι θ).val
      (fun y => (c : EReal) * thetaPshSupremum θ.val (ι y)) :=
    RestrictedApproximantComparison.isThetaPshPotential_smul hV hc
  rw [hRc, hR, ← RestrictedApproximantComparison.diagonalPotentialMass_smul hV hc hcu]
  refine diagonalPotentialMass_congr (closedPullback_smul hι c θ) ?_ hVc hcu
  funext y
  rw [hscale]

include hι in
/-- **`tok-wn:restricted-homogeneous`**, class version: for `ξ ∈ 𝒜_Z` and `c > 0`,
`vol_{X|Z}(cξ) = c^k vol_{X|Z}(ξ)`. -/
theorem classRestrictedVolume_smul (w : KahlerBackground (m + 1) X)
    (hpull : (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)
    (ξ : RealBottChern (m + 1) X) (hbig : IsBigClass ξ)
    (hZ : ∃ y : V, ι y ∉ nonKahlerLocus ξ) {c : ℝ} (hc : 0 < c) :
    classRestrictedVolume ι hι (c • ξ) = ENNReal.ofReal (c ^ k) * classRestrictedVolume ι hι ξ := by
  have hξ : RealBottChern.ofRepresentative (Quotient.out ξ) = ξ := Quotient.out_eq ξ
  have h := restrictedVolume_smul hι w hpull (Quotient.out ξ) (by rw [hξ]; exact hbig)
    (by rw [hξ]; exact hZ) hc
  rw [restrictedVolume_eq_classRestrictedVolume hι, restrictedVolume_eq_classRestrictedVolume hι,
    RealBottChern.ofRepresentative_smul, hξ] at h
  exact h

end Homogeneity

section Flag

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **`tok-wn:restricted-homogeneous`** along `Y₁`: for `ξ ∈ 𝒜_{Y₁}` and `c > 0`,
`vol_{X|Y₁}(cξ) = c^{n-1} vol_{X|Y₁}(ξ)`. -/
theorem firstFlagRestrictedVolume_smul {ξ : RealBottChern (m + 1) F.carrier}
    (hξ : IsBigMeetingFirstDivisor F ξ) {c : ℝ} (hc : 0 < c) :
    firstFlagRestrictedVolume F (c • ξ) = ENNReal.ofReal (c ^ m) * firstFlagRestrictedVolume F ξ := by
  obtain ⟨hbig, hZ⟩ := (isBigMeetingFirstDivisor_iff F ξ).mp hξ
  let : MeasurableSpace F.carrier := borel F.carrier
  have : BorelSpace F.carrier := ⟨rfl⟩
  let : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  have : BorelSpace F.tail.carrier := ⟨rfl⟩
  exact classRestrictedVolume_smul (contMDiff_firstFlagInclusion F) F.omega
    (SubmanifoldKahlerRestriction.isKahler_pullback (Nat.le_succ m) F.firstDivisor.2.2
      F.omega.form F.omega.isKahler) ξ hbig hZ hc

end Flag

end SGPT.Okounkov.TranscendentalWN

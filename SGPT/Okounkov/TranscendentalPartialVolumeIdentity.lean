import SGPT.Okounkov.TranscendentalPartialBirational
import SGPT.Okounkov.TranscendentalPartialExhaustion
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The volume identity and its partial form are equivalent

Source: blueprint node `tok:A-iff-B` (chapter `claude-okounkov-transcendental`), i.e.
Darvas--Reboulet--Witt Nyström--Xia--Zhang, *Transcendental Okounkov bodies* (DRWNXZ), Lemma 5.6:
for a fixed dimension `n = m + 1`,

* `A_n` (`VolumeIdentityAllStatement m`): `vol Δ_{Y•}(ξ) = vol(ξ)/n!` for all `X`, `Y•`, big `ξ`;
* `B_n` (`PartialVolumeIdentityStatement m`): `vol Δ_{Y•}(ξ; R) = (1/n!) ∫_X ⟨R^n⟩` for all `X`,
  `Y•` and Kähler currents `R ∈ 𝒜ᵍ(ξ)`.

`B_n ⇒ A_n` (`volumeIdentityAll_of_partialVolumeIdentity`) is **unconditional**: with the
exhaustion `R_i` of `tok:partial-exhaustion`,
`vol Δ(ξ) = lim vol Δ(ξ; R_i) = lim (1/n!) ∫ ⟨R_i^n⟩ = vol(ξ)/n!`.

`A_n ⇒ B_n` (`partialVolumeIdentity_of_volumeIdentityAll`) uses `tok:partial-birational`, hence
is **conditional** on `PushforwardAnalyticStatement` (RELGEN, via LIFT's `tok:approx-pushforward`;
`..._of_l2Generation`: conditional on RELGEN's `WeaklyPseudoconvexL2GenerationStatement`): `g` has
determinant
`1` and Lebesgue measure is translation invariant, so
`vol Δ(ξ; R) = vol(Δ(ξ; R) g) = vol Δ_{W•}({R'}) = vol({R'})/n!` by `A_n` on `W`; `R'` has bounded
potentials, so `vol({R'}) = ∫_W ⟨R'^n⟩ = ∫_X ⟨R^n⟩`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalPartial

open Set Filter MeasureTheory
open scoped ENNReal Topology Matrix Pointwise Nat
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.TranscendentalRelGen
open SGPT.PSH.VariableComplexAtlas

/-- Right multiplication by a correction matrix preserves Lebesgue measure (`det g = 1`). -/
theorem volume_image_vecMul_correctionMatrixReal {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) (s : Set (Fin n → ℝ)) :
    volume ((fun x => x ᵥ* correctionMatrixReal hπ) '' s) = volume s := by
  have hfun : (fun x : Fin n → ℝ => x ᵥ* correctionMatrixReal hπ) =
      ⇑(Matrix.toLin' (correctionMatrixReal hπ)ᵀ) := by
    funext x
    rw [Matrix.toLin'_apply, Matrix.mulVec_transpose]
  rw [hfun, MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin',
    Matrix.det_transpose, det_correctionMatrixReal, abs_one, ENNReal.ofReal_one, one_mul]

/-- **`tok:A-iff-B`, `B_n ⇒ A_n`** (DRWNXZ Lemma 5.6; unconditional): the partial volume identity
in dimension `n` implies the volume identity `vol Δ(ξ) = vol(ξ)/n!` in dimension `n`. -/
theorem volumeIdentityAll_of_partialVolumeIdentity {m : ℕ}
    (hB : PartialVolumeIdentityStatement.{u} m) : VolumeIdentityAllStatement.{u} m := by
  intro F
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  intro α hα
  set θ := Quotient.out α with hθdef
  have hθ : RealBottChern.ofRepresentative θ = α := Quotient.out_eq α
  have hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ) := by rwa [hθ]
  obtain ⟨R, hR, -, hmass, -, -, hvol⟩ := exists_partialOkounkovBody_exhaustion θ hbig
  have hBi : ∀ i, volume (partialOkounkovBody F θ (R i)) =
      diagonalPotentialMass θ (R i) (isThetaPshPotential_of_mem_gentleCurrents (hR i).1) /
        ((m + 1)! : ℝ≥0∞) := fun i =>
    hB F θ (R i) (gentleKahlerCurrents_subset_globalAnalyticCurrents (hR i)) (hR i).2
  have hlim : Tendsto (fun i => volume (partialOkounkovBody F θ (R i))) atTop
      (𝓝 (sourceClassVolume (RealBottChern.ofRepresentative θ) / ((m + 1)! : ℝ≥0∞))) := by
    refine (ENNReal.Tendsto.div_const hmass (Or.inr ?_)).congr fun i => (hBi i).symm
    exact_mod_cast (Nat.factorial_pos (m + 1)).ne'
  have heq := tendsto_nhds_unique hvol hlim
  change volume (tradOkounkovBody F θ) = _
  rw [heq, hθ]

/-- **`tok:A-iff-B`, `A_n ⇒ B_n`** (DRWNXZ Lemma 5.6), **conditional** on
`PushforwardAnalyticStatement` (through `tok:partial-birational`): the volume identity in
dimension `n` implies the partial volume identity in dimension `n`. -/
theorem partialVolumeIdentity_of_volumeIdentityAll (hP : PushforwardAnalyticStatement.{u}) {m : ℕ} (hA : VolumeIdentityAllStatement.{u} m) :
    PartialVolumeIdentityStatement.{u} m := by
  intro F θ ψ hψ hK
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  obtain ⟨W, π, hπ, D, b, hR⟩ := exists_resolutionData hψ
  let _ : MeasurableSpace W.carrier := borel W.carrier
  have _ : BorelSpace W.carrier := ⟨rfl⟩
  set β := ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature with hβ
  obtain ⟨hbig, himg⟩ := partialOkounkovBody_birational hP hR hK
    (globalAnalyticCurrents_subset_analyticCurrents θ hψ)
  have hAW : volume (tradOkounkovBody W β) =
      sourceClassVolume (RealBottChern.ofRepresentative β) / ((m + 1)! : ℝ≥0∞) := by
    have h := hA W (RealBottChern.ofRepresentative β) hbig
    rwa [← TranscendentalCore.representativeIndependence W β] at h
  obtain ⟨C, hC⟩ := hR.bounded
  calc volume (partialOkounkovBody F θ ψ)
      = volume ((fun x => x ᵥ* correctionMatrixReal hπ) '' partialOkounkovBody F θ ψ) :=
        (volume_image_vecMul_correctionMatrixReal hπ _).symm
    _ = volume (flagValuation W D.weight +ᵥ tradOkounkovBody W β) := by rw [himg]
    _ = volume (tradOkounkovBody W β) := measure_vadd _ _ _
    _ = sourceClassVolume (RealBottChern.ofRepresentative β) / ((m + 1)! : ℝ≥0∞) := hAW
    _ = diagonalPotentialMass β b hR.psh / ((m + 1)! : ℝ≥0∞) := by
        rw [sourceClassVolume_eq_of_bounded W.omega β hR.psh (fun y => (hC y).1)]
    _ = diagonalPotentialMass θ ψ hψ.1 / ((m + 1)! : ℝ≥0∞) := by
        rw [diagonalPotentialMass_residual_eq hR hψ.1]

/-- **`tok:A-iff-B`** (DRWNXZ Lemma 5.6): `A_n ⟺ B_n`, **conditional** (for `⇒`) on
`PushforwardAnalyticStatement`; `⇐` is unconditional
(`volumeIdentityAll_of_partialVolumeIdentity`). -/
theorem volumeIdentity_iff_partialVolumeIdentity (hP : PushforwardAnalyticStatement.{u}) (m : ℕ) :
    VolumeIdentityAllStatement.{u} m ↔ PartialVolumeIdentityStatement.{u} m :=
  ⟨partialVolumeIdentity_of_volumeIdentityAll hP, volumeIdentityAll_of_partialVolumeIdentity⟩

/-- `A_n ⇒ B_n`, **conditional** on RELGEN's `L²` generation theorem
`WeaklyPseudoconvexL2GenerationStatement` (Demailly 2015, Corollary 5.3), the only unproved
input of `PushforwardAnalyticStatement`. -/
theorem partialVolumeIdentity_of_volumeIdentityAll_of_l2Generation
    (hL2 : WeaklyPseudoconvexL2GenerationStatement.{u}) {m : ℕ}
    (hA : VolumeIdentityAllStatement.{u} m) : PartialVolumeIdentityStatement.{u} m :=
  partialVolumeIdentity_of_volumeIdentityAll (pushforwardAnalyticStatement_of_l2Generation hL2) hA

/-- **`tok:A-iff-B`**, conditional on `WeaklyPseudoconvexL2GenerationStatement` (for `⇒`). -/
theorem volumeIdentity_iff_partialVolumeIdentity_of_l2Generation
    (hL2 : WeaklyPseudoconvexL2GenerationStatement.{u}) (m : ℕ) :
    VolumeIdentityAllStatement.{u} m ↔ PartialVolumeIdentityStatement.{u} m :=
  volumeIdentity_iff_partialVolumeIdentity (pushforwardAnalyticStatement_of_l2Generation hL2) m

end SGPT.Okounkov.TranscendentalPartial

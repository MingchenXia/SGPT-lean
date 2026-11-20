import SGPT.Okounkov.TranscendentalVolIdSlice
import SGPT.Okounkov.TranscendentalL2Bridge

/-!
# The volume identity: the induction on the dimension

Package VOL (blueprint `claude-okounkov-transcendental`, nodes `tok:Cn-implies-An` and
`tok:volume-identity`): Darvas--Reboulet--Witt Nyström--Xia--Zhang, *Transcendental Okounkov
bodies* (DRWNXZ), Lemma 7.3 and Theorem 7.6; the book's `thm:Okounkovtranmain` (1).

* `volumeIdentity_succ` (**`tok:Cn-implies-An`**, with `tok:Bn-implies-Cn` and `tok:A-iff-B`):
  for a flag geometry of dimension `n = m + 2`, `A_{n-1}` implies `A_n`, given
  `WNIntegratedStatement F` (Witt Nyström's Theorem C on this `F`) and `PushforwardAnalyticStatement`
  (RELGEN). Fubini (`tok-volid:fubini`): `vol Δ(ξ) = ∫_{ν_min}^{ν_max} vol Δ_t(ξ) dt
  = (1/(n-1)!) ∫ vol_{X|Y₁}(ξ - t{Y₁}) dt = vol(ξ)/n!` (`tok:vol-integral`).
* `volumeIdentityAll_of_dimOne` (**`tok:volume-identity`**, the induction): `A_1` together with
  the WN statements in all dimensions `≥ 2` and `PushforwardAnalyticStatement` give `A_n` for all
  `n`.

`A_1` itself is `tok:A1` (`TranscendentalVolIdPointDegree.volumeIdentity_dimOne`, unconditional);
the final theorem with only the WN (dimensions `≥ 2`) and `L²` hypotheses is
`TranscendentalVolId.volumeIdentity_of_wnIntegrated_of_pushforward`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalVolId

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalSlice
open SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalWN
open SGPT.Okounkov.TranscendentalPartial SGPT.Okounkov.TranscendentalRelGen
open SGPT.PSH.VariableComplexAtlas

/-- **`tok:Cn-implies-An`** (DRWNXZ Lemma 7.3, with Lemma 7.5 and Lemma 5.6): for a flag geometry
`F` of dimension `n = m + 2`, the volume identity in dimension `n - 1` (`A_{n-1}`, for all flag
geometries of dimension `m + 1`) implies the volume identity on `F`, given Witt Nyström's
Theorem C on `F` (`WNIntegratedStatement F`) and RELGEN's `PushforwardAnalyticStatement`. -/
theorem volumeIdentity_succ {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 2)} (hWN : WNIntegratedStatement F)
    (hA : VolumeIdentityAllStatement.{u} m) (hP : PushforwardAnalyticStatement.{u}) :
    VolumeIdentityStatement F := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  intro α hα
  set θ := Quotient.out α with hθdef
  have hθ : RealBottChern.ofRepresentative θ = α := Quotient.out_eq α
  have hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ) := by rwa [hθ]
  obtain ⟨φ, hφ⟩ := TranscendentalBody.exists_mem_gentleKahlerCurrents_of_isBig hbig
  obtain ⟨E, hE⟩ := exists_isFirstDivisorUnitMetric F hφ.1.1
  have hproj := image_first_tradOkounkovBody_eq_Icc (F := F) hbig
  have hV := sourceClassVolume_eq_lintegral_restrictedVolume (F := F) hWN hbig hE
  change volume (tradOkounkovBody F θ) = _
  rw [← hθ]
  exact volume_eq_div_factorial_of_sliceIdentity (isClosed_tradOkounkovBody θ).measurableSet
    hproj.le (shiftedRestrictedVolume θ E) _ hV
    (fun t ht => restrictedVolume_eq_volume_slice hWN hA hP hbig hE ht)

/-- **`tok:volume-identity`, the induction** (DRWNXZ Theorem 7.6): `A_1`, Witt Nyström's
Theorem C on every flag geometry of dimension `≥ 2` and `PushforwardAnalyticStatement` give the
volume identity `vol Δ_{Y•}(α) = vol(α)/n!` in every dimension. -/
theorem volumeIdentityAll_of_dimOne
    (hWN : ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 2)), WNIntegratedStatement F)
    (hP : PushforwardAnalyticStatement.{u}) (hA₁ : VolumeIdentityAllStatement.{u} 0) :
    ∀ m : ℕ, VolumeIdentityAllStatement.{u} m := by
  intro m
  induction m with
  | zero => exact hA₁
  | succ m ih => exact fun F => volumeIdentity_succ (hWN m F) ih hP

end SGPT.Okounkov.TranscendentalVolId

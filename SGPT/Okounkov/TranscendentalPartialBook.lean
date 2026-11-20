import SGPT.Okounkov.TranscendentalPartialVolumeIdentity

/-!
# The book's partial Okounkov bodies of Kähler currents with analytic singularities

Source: the book's `def:POBanalsing`, `lma:Okounkov:L1426` and `lma:Okounkovanalycomp`
(chapter *The theory of Okounkov bodies*, section *Transcendental partial Okounkov bodies*,
lines 1411--1510).

For a Kähler current `T = θ + dd^c ψ` with analytic singularities (of a global type,
`ψ ∈ 𝒜ᵍ(θ)`), `def:POBanalsing` chooses a modification `π : Y → X` with `π^*T = [D] + R`
(`D` an effective `ℚ`-divisor, `R` closed positive with bounded potential) along which the
lifting `(Z•, g)` of the flag exists, and sets
`Δ_{Y•}(T) = Δ_{Z•}({R}) g⁻¹ + ν_{Z•}([D]) g⁻¹`.

* `analyticPartialBodyOf`: the right-hand side for given data (`IsResolutionData`);
* `analyticPartialBody`: the book's definition (data chosen; they exist by
  `tok:resolution-lifting`, `exists_resolutionData`);
* `analyticPartialBodyOf_eq_partialOkounkovBody`: for every choice of data, the book's body is
  the DRWNXZ partial body `Δ(ξ; T) = closure ν(Ω(ξ; T))` (`tok:partial-birational`); hence
  `analyticPartialBodyOf_eq_of_resolutionData` (`lma:Okounkov:L1426`, independence of `π`);
* `analyticPartialBody_subset` (`lma:Okounkovanalycomp`, inclusions) and
  `volume_analyticPartialBody` (`lma:Okounkovanalycomp`, `vol Δ(T) = (1/n!) ∫ T^n`).

All of these are **conditional** on `PushforwardAnalyticStatement` (RELGEN's
`tok:boucksom-pushforward`, the input of `thm:Okounkovtranmain` (3)); the volume formula is in
addition conditional on the volume identity `VolumeIdentityAllStatement m`
(`thm:Okounkovtranmain` (1)), exactly as in the book, whose proofs use items (1) and (3).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalPartial

open Set Filter MeasureTheory
open scoped ENNReal Topology Matrix Pointwise Nat
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.TranscendentalRelGen

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- **The book's formula `eq:POBanalsing`** for given resolution data: for a lifting
`(W•, g)` along `π` and a metered divisor `D` on `W`,
`Δ_{W•}({π^*θ - Θ_D}) g⁻¹ + ν_{W•}([D]) g⁻¹`; for resolution data of `T = θ + dd^c ψ`
(`π^*T = [D] + R`, `{R} = {π^*θ - Θ_D}`) this is `Δ_{Z•}({R}) g⁻¹ + ν_{Z•}([D]) g⁻¹`. -/
def analyticPartialBodyOf (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    {W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π)
    (D : MeteredEffectiveQDivisor (m + 1) W.carrier) : Set (Fin (m + 1) → ℝ) :=
  (flagValuation W D.weight ᵥ* (correctionMatrixReal hπ)⁻¹) +ᵥ
    ((fun x => x ᵥ* (correctionMatrixReal hπ)⁻¹) ''
      tradOkounkovBody W (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature))

open scoped Classical in
/-- **The book's partial Okounkov body of a Kähler current with analytic singularities**
(`def:POBanalsing`): `Δ_{Y•}(T) = Δ_{Z•}({R}) g⁻¹ + ν_{Z•}([D]) g⁻¹` for a chosen modification
`π : Z → X` with `π^*T = [D] + R` along which the lifting `(Z•, g)` exists (such data exist for
`ψ ∈ 𝒜ᵍ(θ)`, `exists_resolutionData`; the choice does not matter,
`analyticPartialBodyOf_eq_of_resolutionData`). Empty if there are no such data. -/
def analyticPartialBody (F : OriginalFlagGeometry.{u} (m + 1))
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (ψ : F.carrier → EReal) :
    Set (Fin (m + 1) → ℝ) :=
  if h : ∃ (W : OriginalFlagGeometry.{u} (m + 1)) (π : W.carrier → F.carrier)
      (hπ : IsFlagLifting F W π) (D : MeteredEffectiveQDivisor (m + 1) W.carrier)
      (b : W.carrier → EReal), IsResolutionData θ ψ hπ D b then
    analyticPartialBodyOf θ h.choose_spec.choose_spec.choose
      h.choose_spec.choose_spec.choose_spec.choose
  else ∅

/-- `(Δ g)g⁻¹ = Δ`. -/
theorem image_vecMul_inv_image_vecMul {n : ℕ} {W : OriginalFlagGeometry.{u} n}
    {F' : OriginalFlagGeometry.{u} n} {π : W.carrier → F'.carrier} (hπ : IsFlagLifting F' W π)
    (s : Set (Fin n → ℝ)) :
    (fun x => x ᵥ* (correctionMatrixReal hπ)⁻¹) ''
      ((fun x => x ᵥ* correctionMatrixReal hπ) '' s) = s := by
  rw [image_image]
  conv_rhs => rw [← image_id s]
  exact image_congr fun x _ => vecMul_correctionMatrixReal_inv hπ x

/-- `Δ g⁻¹ + ν g⁻¹ = (ν + Δ) g⁻¹`. -/
theorem analyticPartialBodyOf_eq_image (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    {W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π)
    (D : MeteredEffectiveQDivisor (m + 1) W.carrier) :
    analyticPartialBodyOf θ hπ D = (fun x => x ᵥ* (correctionMatrixReal hπ)⁻¹) ''
      (flagValuation W D.weight +ᵥ
        tradOkounkovBody W (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature)) := by
  rw [analyticPartialBodyOf, ← image_vadd, ← image_vadd, image_image, image_image]
  refine image_congr fun x _ => ?_
  simp only [vadd_eq_add, Matrix.add_vecMul]

/-- **The book's body is the DRWNXZ partial body** (`tok:partial-birational`), for every choice of
resolution data; **conditional** on `PushforwardAnalyticStatement`. -/
theorem analyticPartialBodyOf_eq_partialOkounkovBody (hP : PushforwardAnalyticStatement.{u})
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {ψ : F.carrier → EReal}
    {W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier} {hπ : IsFlagLifting F W π}
    {D : MeteredEffectiveQDivisor (m + 1) W.carrier} {b : W.carrier → EReal}
    (hR : IsResolutionData θ ψ hπ D b) (hK : IsKahlerCurrentPotential θ ψ)
    (hA : ψ ∈ analyticCurrents θ) :
    analyticPartialBodyOf θ hπ D = partialOkounkovBody F θ ψ := by
  obtain ⟨-, himg⟩ := partialOkounkovBody_birational hP hR hK hA
  have h := congrArg (fun s => (fun x => x ᵥ* (correctionMatrixReal hπ)⁻¹) '' s) himg
  rw [image_vecMul_inv_image_vecMul] at h
  rw [h, analyticPartialBodyOf_eq_image]

/-- **`lma:Okounkov:L1426`** (independence of the modification), **conditional** on
`PushforwardAnalyticStatement`: two choices of resolution data of a Kähler current
`T ∈ 𝒜(ξ)` give the same body `Δ_{Z•}({R}) g⁻¹ + ν_{Z•}([D]) g⁻¹`. -/
theorem analyticPartialBodyOf_eq_of_resolutionData (hP : PushforwardAnalyticStatement.{u})
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {ψ : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential θ ψ) (hA : ψ ∈ analyticCurrents θ)
    {W₁ : OriginalFlagGeometry.{u} (m + 1)} {π₁ : W₁.carrier → F.carrier}
    {hπ₁ : IsFlagLifting F W₁ π₁} {D₁ : MeteredEffectiveQDivisor (m + 1) W₁.carrier}
    {b₁ : W₁.carrier → EReal} (hR₁ : IsResolutionData θ ψ hπ₁ D₁ b₁)
    {W₂ : OriginalFlagGeometry.{u} (m + 1)} {π₂ : W₂.carrier → F.carrier}
    {hπ₂ : IsFlagLifting F W₂ π₂} {D₂ : MeteredEffectiveQDivisor (m + 1) W₂.carrier}
    {b₂ : W₂.carrier → EReal} (hR₂ : IsResolutionData θ ψ hπ₂ D₂ b₂) :
    analyticPartialBodyOf θ hπ₁ D₁ = analyticPartialBodyOf θ hπ₂ D₂ := by
  rw [analyticPartialBodyOf_eq_partialOkounkovBody hP hR₁ hK hA,
    analyticPartialBodyOf_eq_partialOkounkovBody hP hR₂ hK hA]

/-- **The book's body of `def:POBanalsing` is the DRWNXZ partial body**, **conditional** on
`PushforwardAnalyticStatement`: for a Kähler current `T = θ + dd^c ψ`, `ψ ∈ 𝒜ᵍ(θ)`,
`Δ_{Y•}(T) = Δ_{Y•}(ξ; T)`. -/
theorem analyticPartialBody_eq_partialOkounkovBody (hP : PushforwardAnalyticStatement.{u})
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {ψ : F.carrier → EReal}
    (hψ : ψ ∈ globalAnalyticCurrents θ) (hK : IsKahlerCurrentPotential θ ψ) :
    analyticPartialBody F θ ψ = partialOkounkovBody F θ ψ := by
  classical
  have h : ∃ (W : OriginalFlagGeometry.{u} (m + 1)) (π : W.carrier → F.carrier)
      (hπ : IsFlagLifting F W π) (D : MeteredEffectiveQDivisor (m + 1) W.carrier)
      (b : W.carrier → EReal), IsResolutionData θ ψ hπ D b := exists_resolutionData hψ
  rw [analyticPartialBody, dif_pos h]
  exact analyticPartialBodyOf_eq_partialOkounkovBody hP
    h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec hK
    (globalAnalyticCurrents_subset_analyticCurrents θ hψ)

/-- **`lma:Okounkovanalycomp`, inclusions**, **conditional** on `PushforwardAnalyticStatement`:
for Kähler currents `T ⪯ S` in `𝒜ᵍ(ξ)`, `Δ_{Y•}(T) ⊆ Δ_{Y•}(S) ⊆ Δ_{Y•}(α)`. -/
theorem analyticPartialBody_subset (hP : PushforwardAnalyticStatement.{u})
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {χ ψ : F.carrier → EReal}
    (hχ : χ ∈ globalAnalyticCurrents θ) (hKχ : IsKahlerCurrentPotential θ χ)
    (hψ : ψ ∈ globalAnalyticCurrents θ) (hKψ : IsKahlerCurrentPotential θ ψ)
    (hχψ : SingularityLE χ ψ) :
    analyticPartialBody F θ χ ⊆ analyticPartialBody F θ ψ ∧
      analyticPartialBody F θ ψ ⊆ tradOkounkovBody F θ := by
  rw [analyticPartialBody_eq_partialOkounkovBody hP hχ hKχ,
    analyticPartialBody_eq_partialOkounkovBody hP hψ hKψ]
  exact ⟨partialOkounkovBody_mono θ hχψ, partialOkounkovBody_subset_tradOkounkovBody θ ψ⟩

/-- **`lma:Okounkovanalycomp`, volume** (`eq:volpobanaly`), **conditional** on
`PushforwardAnalyticStatement` and on the volume identity in dimension `n`
(`VolumeIdentityAllStatement m`, `thm:Okounkovtranmain` (1)): for a Kähler current `T ∈ 𝒜ᵍ(ξ)`,
`vol Δ_{Y•}(T) = (1/n!) ∫_X ⟨T^n⟩`. -/
theorem volume_analyticPartialBody (hP : PushforwardAnalyticStatement.{u})
    (hA : VolumeIdentityAllStatement.{u} m) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {ψ : F.carrier → EReal} (hψ : ψ ∈ globalAnalyticCurrents θ)
    (hK : IsKahlerCurrentPotential θ ψ) :
    letI : MeasurableSpace F.carrier := borel F.carrier
    haveI : BorelSpace F.carrier := ⟨rfl⟩
    volume (analyticPartialBody F θ ψ) = diagonalPotentialMass θ ψ hψ.1 / ((m + 1)! : ℝ≥0∞) := by
  rw [analyticPartialBody_eq_partialOkounkovBody hP hψ hK]
  exact partialVolumeIdentity_of_volumeIdentityAll hP hA F θ ψ hψ hK

/-- `x (g h) h⁻¹ = x g`. -/
theorem image_vecMul_inv_image_vecMul_mul {n : ℕ} {W V : OriginalFlagGeometry.{u} n}
    {p : V.carrier → W.carrier} (hp : IsFlagLifting W V p)
    (g : Matrix (Fin n) (Fin n) ℝ) (s : Set (Fin n → ℝ)) :
    (fun x => x ᵥ* (correctionMatrixReal hp)⁻¹) ''
      ((fun x => x ᵥ* (g * correctionMatrixReal hp)) '' s) = (fun x => x ᵥ* g) '' s := by
  rw [image_image]
  refine image_congr fun x _ => ?_
  rw [Matrix.vecMul_vecMul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_det_correctionMatrixReal hp), Matrix.mul_one]

/-- **`lma:liftOkounana` for given data**, **conditional** on `PushforwardAnalyticStatement`: for a
Kähler current `T = θ + dd^c ψ ∈ 𝒜(ξ)`, a lifting `(W•, g)` along `π : W → X` and resolution data
of `π^*T` along a lifting `(V•, h)` of `W•` (`π^*T` itself need not be a Kähler current), the
book's formula for `π^*T` gives `Δ_{Y•}(ξ; T) g`: the composite `π ∘ p` carries resolution data of
`T` with correction `g h` (`flagLifting_comp_correction`). -/
theorem analyticPartialBodyOf_pullback (hP : PushforwardAnalyticStatement.{u})
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {ψ : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential θ ψ) (hA : ψ ∈ analyticCurrents θ)
    {W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π)
    {V : OriginalFlagGeometry.{u} (m + 1)} {p : V.carrier → W.carrier} {hp : IsFlagLifting W V p}
    {D : MeteredEffectiveQDivisor (m + 1) V.carrier} {b : V.carrier → EReal}
    (hR : IsResolutionData (ClosedRealOneOneForm.pullback hπ.1.1 θ) (fun y => ψ (π y)) hp D b) :
    analyticPartialBodyOf (ClosedRealOneOneForm.pullback hπ.1.1 θ) hp D =
      (fun x => x ᵥ* correctionMatrixReal hπ) '' partialOkounkovBody F θ ψ := by
  obtain ⟨hπp, hcor⟩ := flagLifting_comp_correction hπ hp
  have hgeom : (ClosedRealOneOneForm.pullback hπp.1.1 θ - D.curvature).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback hp.1.1 (ClosedRealOneOneForm.pullback hπ.1.1 θ) -
        D.curvature).val :=
    geometricallyEq_sub (SmoothRealForm.pullback_comp_geometricallyEq hπ.1.1 hp.1.1 θ.val) _
  have hR' : IsResolutionData θ ψ hπp D b :=
    ⟨(hgeom.thetaPshPotential_iff b).mpr hR.psh, hR.bounded, fun y => hR.eq y⟩
  obtain ⟨-, himg⟩ := partialOkounkovBody_birational hP hR' hK hA
  rw [tradOkounkovBody_eq_of_class_eq (RealBottChern.ofRepresentative_eq_of_geometricallyEq hgeom),
    hcor] at himg
  rw [analyticPartialBodyOf_eq_image, ← himg, image_vecMul_inv_image_vecMul_mul]

/-- **`lma:liftOkounana`** (bimeromorphic behaviour of `def:POBanalsing`), **conditional** on
`PushforwardAnalyticStatement`: for a Kähler current `T = θ + dd^c ψ`, `ψ ∈ 𝒜ᵍ(θ)`, and a proper
bimeromorphic `π : W → X` from a compact Kähler manifold carrying the lifting `(W•, g)`,
`Δ_{W•}(π^*T) = Δ_{Y•}(T) g` (both sides by the book's formula `eq:POBanalsing`; for `π^*T`,
which is in general not a Kähler current, the formula is applied as it stands). -/
theorem analyticPartialBody_pullback (hP : PushforwardAnalyticStatement.{u})
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {ψ : F.carrier → EReal}
    (hψ : ψ ∈ globalAnalyticCurrents θ) (hK : IsKahlerCurrentPotential θ ψ)
    {W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) :
    analyticPartialBody W (ClosedRealOneOneForm.pullback hπ.1.1 θ) (fun y => ψ (π y)) =
      (fun x => x ᵥ* correctionMatrixReal hπ) '' analyticPartialBody F θ ψ := by
  classical
  have hψπ : (fun y => ψ (π y)) ∈ globalAnalyticCurrents (ClosedRealOneOneForm.pullback hπ.1.1 θ) :=
    comp_mem_globalAnalyticCurrents hπ.1 hψ
  have h : ∃ (V : OriginalFlagGeometry.{u} (m + 1)) (p : V.carrier → W.carrier)
      (hp : IsFlagLifting W V p) (D : MeteredEffectiveQDivisor (m + 1) V.carrier)
      (b : V.carrier → EReal), IsResolutionData (ClosedRealOneOneForm.pullback hπ.1.1 θ)
        (fun y => ψ (π y)) hp D b := exists_resolutionData hψπ
  rw [analyticPartialBody, dif_pos h, analyticPartialBody_eq_partialOkounkovBody hP hψ hK]
  exact analyticPartialBodyOf_pullback hP hK (globalAnalyticCurrents_subset_analyticCurrents θ hψ)
    hπ h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

end SGPT.Okounkov.TranscendentalPartial

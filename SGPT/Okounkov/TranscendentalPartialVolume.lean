import SGPT.Okounkov.TranscendentalPartialDefs
import SGPT.Okounkov.TranscendentalVolumeConcavityACVolume
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling
import SGPT.Foundations.Analysis.Pending.AmbientConvexCurrent
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof

/-!
# The volume as a supremum over gentle Kähler currents

Source: blueprint node `tok:volume-sup` (chapter `claude-okounkov-transcendental`): agreement of
the book's volume of a class (`def:volcohclass`, `sourceClassVolume`) with the volume used in
Darvas--Reboulet--Witt Nyström--Xia--Zhang, *Transcendental Okounkov bodies* (DRWNXZ, §2,
after Boucksom): for `ξ = {θ}` big,
`vol(ξ) = sup_{T ∈ Ω(ξ)} ∫_X ⟨T^n⟩`.

* `diagonalPotentialMass_le_sourceClassVolume` (VOLCONC) gives `≤`: every potential is more
  singular than `V_θ`.
* `≥` (`sourceClassVolume_le_iSup_gentleKahler`): for a Kähler current `θ + dd^c ψ ≥ c ω` and
  `s ∈ (0, 1)`, `u = s V_θ + (1 - s) ψ ∈ PSH(X, θ - (1 - s) c ω)` has mass at least
  `s^n vol(ξ)` (multilinearity, `globalMixedMeasure_diagonal_convexComb_le`); a gentle
  quasi-equisingular approximation `v_j ≥ u` of `u` (`thm:qequi`, positive indices) lies in
  `Ω(ξ)` for large `j` and has mass at least that of `u` (monotonicity of non-pluripolar masses);
  let `s → 1`. This replaces the blueprint's appeal to the convergence of the masses of a
  quasi-equisingular approximation (`thm:source-i-volume-and-mass-positive-limit`): only the
  monotonicity of masses is needed.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalPartial

open Set Filter MeasureTheory
open scoped ENNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.PSH SGPT.Okounkov.TranscendentalCore
open SGPT.PSH.VariableComplexAtlas

section Manifold

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- `sup_{T ∈ Ω(ξ)} ∫ ⟨T^n⟩ ≤ vol ξ`. -/
theorem iSup_gentleKahler_le_sourceClassVolume (ω : KahlerBackground (m + 1) X)
    (θ : ClosedRealOneOneForm (m + 1) X) :
    (⨆ (φ : X → EReal) (hφ : φ ∈ gentleKahlerCurrents θ),
        diagonalPotentialMass θ φ (isThetaPshPotential_of_mem_gentleCurrents hφ.1)) ≤
      sourceClassVolume (RealBottChern.ofRepresentative θ) :=
  iSup₂_le fun _ hφ => TranscendentalVolumeConcavity.diagonalPotentialMass_le_sourceClassVolume
    ω θ (isThetaPshPotential_of_mem_gentleCurrents hφ.1)

/-- **`tok:volume-sup`, `≥`**: if `Ω(ξ) ≠ ∅` (e.g. `ξ` big), then
`vol ξ ≤ sup_{T ∈ Ω(ξ)} ∫ ⟨T^n⟩`. -/
theorem sourceClassVolume_le_iSup_gentleKahler (w : KahlerBackground (m + 1) X)
    (θ : ClosedRealOneOneForm (m + 1) X) (hΩ : (gentleKahlerCurrents θ).Nonempty) :
    sourceClassVolume (RealBottChern.ofRepresentative θ) ≤
      ⨆ (φ : X → EReal) (hφ : φ ∈ gentleKahlerCurrents θ),
        diagonalPotentialMass θ φ (isThetaPshPotential_of_mem_gentleCurrents hφ.1) := by
  classical
  obtain ⟨ψ, -, κ, hψκ⟩ := hΩ
  -- `κ ≥ c w`
  obtain ⟨A, hA, hAsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ (-w.form)
  set c : ℝ := A⁻¹ with hc
  have hc0 : 0 < c := inv_pos.mpr hA
  have hκc : (κ.form - c • w.form).val.IsSemipositive := by
    have h := KahlerDomination.isSemipositive_smul hAsemi hc0.le
    have he : c • (-w.form + A • κ.form) = κ.form - c • w.form := by
      rw [smul_add, smul_smul, hc, inv_mul_cancel₀ hA.ne', one_smul, smul_neg]
      abel
    rwa [he] at h
  have hψ : IsThetaPshPotential (θ - c • w.form).val ψ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hψκ hκc
    have he : θ - κ.form + (κ.form - c • w.form) = θ - c • w.form := by abel
    rwa [he] at h
  have hψθ : IsThetaPshPotential θ.val ψ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hψ
      (KahlerDomination.isSemipositive_smul w.isSemipositive hc0.le)
    rwa [sub_add_cancel] at h
  -- `vol ξ = ∫ ⟨θ_{V_θ}^n⟩`
  obtain ⟨hV, hvol⟩ := TranscendentalVolumeConcavity.sourceClassVolume_ofRepresentative w θ hψθ
  rw [hvol]
  set S : ℝ≥0∞ := ⨆ (φ : X → EReal) (hφ : φ ∈ gentleKahlerCurrents θ),
    diagonalPotentialMass θ φ (isThetaPshPotential_of_mem_gentleCurrents hφ.1) with hS
  -- the lower bound for each `s ∈ (0, 1)`
  have hbound : ∀ s : ℝ, 0 < s → s < 1 →
      ENNReal.ofReal (s ^ (m + 1)) * diagonalPotentialMass θ (thetaPshSupremum θ.val) hV ≤ S := by
    intro s hs0 hs1
    set u : X → EReal := ThetaPshConvexCombination.convexComb s (thetaPshSupremum θ.val) ψ
      with hudef
    set d : ℝ := (1 - s) * c with hd
    have hd0 : 0 < d := mul_pos (sub_pos.mpr hs1) hc0
    have hV0 : IsThetaPshPotential (θ - (0 : ℝ) • w.form).val (thetaPshSupremum θ.val) := by
      rwa [zero_smul, sub_zero]
    have hu : IsThetaPshPotential (θ - d • w.form).val u := by
      have h := AmbientConvexCurrent.isThetaPshPotential_convexComb_sub_smul w hs0 hs1 hV0 hψ
      rwa [mul_zero, zero_add] at h
    obtain ⟨v, hqea, hgentle⟩ :=
      SGPT.PSH.exists_sourceGentleQuasiEquisingularApproximation w (θ - d • w.form) hu
    obtain ⟨-, -, hdec, ⟨w', ε, hε, hterm⟩, -⟩ := hqea
    obtain ⟨A', hA', hA'semi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul w (-w'.form)
    have hεlim : Tendsto (fun j => ε j * A') atTop (𝓝 0) := by
      simpa only [zero_mul] using hε.2.2.mul_const A'
    obtain ⟨j, hj⟩ := (hεlim.eventually (eventually_le_nhds (half_pos hd0))).exists
    have hvj : IsThetaPshPotential (θ - (d / 2) • w.form).val (v j) := by
      have h1 := LocalPotentials.isThetaPshPotential_add_of_semipositive (hterm j)
        (KahlerDomination.isSemipositive_smul hA'semi (hε.1 j))
      have h2 := LocalPotentials.isThetaPshPotential_add_of_semipositive h1
        (KahlerDomination.isSemipositive_smul w.isSemipositive (sub_nonneg.mpr hj))
      have he : θ - d • w.form + ε j • w'.form + ε j • (-w'.form + A' • w.form) +
          (d / 2 - ε j * A') • w.form = θ - (d / 2) • w.form := by
        rw [smul_add, smul_neg, smul_smul, sub_smul]
        module
      rwa [he] at h2
    have hvjθ : IsThetaPshPotential θ.val (v j) := by
      have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hvj
        (KahlerDomination.isSemipositive_smul w.isSemipositive (half_pos hd0).le)
      rwa [sub_add_cancel] at h
    have hmem : v j ∈ gentleKahlerCurrents θ := by
      refine ⟨⟨hvjθ, _, _, hgentle j⟩, KahlerBackground.smul (half_pos hd0) w, ?_⟩
      rwa [KahlerBackground.smul_form]
    have hge : ∀ x, u x ≤ v j x := fun x => (hdec.1 x).le_of_tendsto (hdec.2 x) j
    have huθ : IsThetaPshPotential θ.val u :=
      ThetaPshConvexCombination.isThetaPshPotential_convexComb hV hψθ hs0 hs1
    have hconv := GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le
      hV hψθ hs0 hs1 univ
    calc ENNReal.ofReal (s ^ (m + 1)) * diagonalPotentialMass θ (thetaPshSupremum θ.val) hV
        ≤ diagonalPotentialMass θ u huθ := hconv
      _ ≤ diagonalPotentialMass θ (v j) hvjθ :=
          diagonalPotentialMass_mono_of_kahler w huθ hvjθ
            (MoreSingularOn.of_le fun x _ => hge x)
      _ ≤ S := le_iSup₂_of_le (f := fun (φ : X → EReal) (hφ : φ ∈ gentleKahlerCurrents θ) =>
            diagonalPotentialMass θ φ (isThetaPshPotential_of_mem_gentleCurrents hφ.1))
            (v j) hmem le_rfl
  -- `s → 1`
  have hlim : Tendsto (fun s : ℝ => ENNReal.ofReal (s ^ (m + 1)) *
      diagonalPotentialMass θ (thetaPshSupremum θ.val) hV) (𝓝[<] 1)
      (𝓝 (ENNReal.ofReal ((1 : ℝ) ^ (m + 1)) *
        diagonalPotentialMass θ (thetaPshSupremum θ.val) hV)) := by
    apply ENNReal.Tendsto.mul_const _ (Or.inr (MixedMass.globalMixedMass_lt_top w _).ne)
    exact ((ENNReal.continuous_ofReal.comp (continuous_pow (m + 1))).tendsto 1).mono_left
      nhdsWithin_le_nhds
  rw [one_pow, ENNReal.ofReal_one, one_mul] at hlim
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with s hs
  exact hbound s hs.1 hs.2

/-- **`tok:volume-sup`** (agreement of `def:volcohclass` with DRWNXZ's volume): if `Ω(ξ) ≠ ∅`
(e.g. `ξ` big), then `vol ξ = sup_{T ∈ Ω(ξ)} ∫_X ⟨T^n⟩`. -/
theorem sourceClassVolume_eq_iSup_gentleKahler (w : KahlerBackground (m + 1) X)
    (θ : ClosedRealOneOneForm (m + 1) X) (hΩ : (gentleKahlerCurrents θ).Nonempty) :
    sourceClassVolume (RealBottChern.ofRepresentative θ) =
      ⨆ (φ : X → EReal) (hφ : φ ∈ gentleKahlerCurrents θ),
        diagonalPotentialMass θ φ (isThetaPshPotential_of_mem_gentleCurrents hφ.1) :=
  le_antisymm (sourceClassVolume_le_iSup_gentleKahler w θ hΩ)
    (iSup_gentleKahler_le_sourceClassVolume w θ)

end Manifold

section Flag

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **`tok:volume-sup`** for a flag geometry and a big class `ξ = {θ}` (the form used by
DRWNXZ, §5): `vol ξ = sup_{T ∈ Ω(ξ)} ∫_X ⟨T^n⟩` (Borel measurable structure on `X`). -/
theorem classVolume_eq_iSup_gentleKahler (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    letI : MeasurableSpace F.carrier := borel F.carrier
    haveI : BorelSpace F.carrier := ⟨rfl⟩
    sourceClassVolume (RealBottChern.ofRepresentative θ) =
      ⨆ (φ : F.carrier → EReal) (hφ : φ ∈ gentleKahlerCurrents θ),
        diagonalPotentialMass θ φ (isThetaPshPotential_of_mem_gentleCurrents hφ.1) := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  exact sourceClassVolume_eq_iSup_gentleKahler F.omega θ
    (TranscendentalBody.exists_mem_gentleKahlerCurrents_of_isBig hbig)

end Flag

end SGPT.Okounkov.TranscendentalPartial

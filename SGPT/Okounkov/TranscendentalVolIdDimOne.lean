import SGPT.Okounkov.TranscendentalVolIdInduction
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalGlobalMixedMass

/-!
# The volume identity in dimension one, from the integrated derivative formula

Package VOL (blueprint `claude-tok-volid`, nodes `tok-volid:point-restricted`,
`tok-volid:A1-wn`): on a compact Kähler curve with flag `X ⊇ {q}`, the restricted volume along
the point `q` is `1` and the slices of `Δ(ξ) ⊆ ℝ` are points, so the integrated formula
`vol(ξ) = ∫_{ν_min}^{ν_max} vol_{X|q}(ξ - t{q}) dt` (Witt Nyström's Theorem C in dimension one,
`WNIntegratedStatement F`) gives `vol Δ(ξ) = ν_max - ν_min = vol(ξ)`.

* `exists_gentleKahler_restrict` (any dimension): for rational `t ∈ (ν_min, ν_max)` there is a
  gentle Kähler current in `ξ - t{Y₁}` whose potential is not `-∞` on `Y₁`;
* `shiftedRestrictedVolume_eq_one` (dimension one): `vol_{X|q}(ξ - t{q}) = 1` on
  `(ν_min, ν_max)` (the non-pluripolar mass on a point is the counting measure, TN
  `global_empty_mixed_measure_eq_count`);
* `volumeIdentity_dimOne_of_wn`: `A_1`, **conditional on `WNIntegratedStatement F`** for the curve.

The unconditional `A_1` (DRWNXZ Lemma 3.6, through the volume on a curve and the degree of a
point) is `TranscendentalVolIdPointDegree.volumeIdentity_dimOne`; it removes this use of WN21 in
dimension one.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalVolId

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalSlice
open SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalWN
open SGPT.Okounkov.TranscendentalPartial SGPT.Okounkov.TranscendentalRelGen
open SGPT.PSH SGPT.PSH.VariableComplexAtlas

section Genuine

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- A gentle Kähler current of `ξ` with first coordinate exactly `t` (`tok-slice:fixed-first`). -/
theorem exists_mem_fixedFirst {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {t : ℚ} (h₁ : firstValuationMin F θ < t) (h₂ : (t : ℝ) < firstValuationMax F θ) :
    ∃ S ∈ gentleKahlerCurrents θ, flagValuation F S 0 = t := by
  obtain ⟨_, ⟨P, hP, rfl⟩, hPt⟩ := exists_lt_of_csInf_lt (firstValuations_nonempty hbig) h₁
  obtain ⟨_, ⟨T, hT, rfl⟩, hTt⟩ := exists_lt_of_lt_csSup (firstValuations_nonempty hbig) h₂
  obtain ⟨p, -, hp⟩ := flagValuation_rational_of_analytic (m + 1) F θ P
    (gentleCurrents_subset_analyticCurrents θ hP.1) 0
  obtain ⟨q, -, hq⟩ := flagValuation_rational_of_analytic (m + 1) F θ T
    (gentleCurrents_subset_analyticCurrents θ hT.1) 0
  have hpt : p < t := by
    change flagValuation F P 0 < t at hPt
    rw [hp] at hPt; exact_mod_cast hPt
  have htq : t ≤ q := by
    change (t : ℝ) < flagValuation F T 0 at hTt
    rw [hq] at hTt; exact_mod_cast hTt.le
  obtain ⟨S, hS, hSt, -⟩ := exists_mem_fixedFirst_near hT hP hq hp (Or.inl ⟨hpt, htq⟩) 0
  exact ⟨S, hS, hSt⟩

/-- For rational `t ∈ (ν_min, ν_max)` there is `ψ ∈ Ω(ξ - t{Y₁})` with `ψ|_{Y₁}` a genuine
potential (so `vol_{X|Y₁}(ξ - t{Y₁})` is a supremum over a nonempty family). -/
theorem exists_gentleKahler_restrict {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {t : ℚ} (h₁ : firstValuationMin F θ < t) (h₂ : (t : ℝ) < firstValuationMax F θ) :
    ∃ ψ ∈ gentleKahlerCurrents (θ - (t : ℝ) • E.curvature),
      IsThetaPshPotential (firstFlagRestriction F (θ - (t : ℝ) • E.curvature)).val
        (restrictFirst F ψ) := by
  obtain ⟨S, hS, hSt⟩ := exists_mem_fixedFirst hbig h₁ h₂
  obtain ⟨v, ⟨κ, hκ⟩, -, hwA, -, -⟩ := exists_residual_of_fixedFirst hE hS hSt
  obtain ⟨ψ, hψ, -, hle⟩ := TranscendentalBody.exists_mem_gentleKahlerCurrents_ge hκ
  refine ⟨ψ, hψ, isThetaPshPotential_restrict hψ.1.1.1 hwA.1.2 ⟨0, fun y _ => ?_⟩⟩
  simpa using hle (firstFlagInclusion F y)

end Genuine

section DimOne

variable {F : OriginalFlagGeometry.{u} 1}

/-- The non-pluripolar mass of any potential on the point `Y₁` is `1`. -/
theorem diagonalPotentialMass_point_eq_one {θ' : ClosedRealOneOneForm 0 F.tail.carrier}
    {u' : F.tail.carrier → EReal} (hu' : IsThetaPshPotential θ'.val u') :
    (letI : MeasurableSpace F.tail.carrier := borel F.tail.carrier
     haveI : BorelSpace F.tail.carrier := ⟨rfl⟩
     diagonalPotentialMass θ' u' hu') = 1 := by
  let _ : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  have _ : BorelSpace F.tail.carrier := ⟨rfl⟩
  have h := (ZeroDimensionalGlobalMixedMass.global_empty_mixed_measure_eq_count
    (fun _ : Fin 0 => θ') (fun _ => u') (fun _ => hu'.1)).2.1
  have hdisc := (ZeroDimensionalGlobalMixedMass.compact_zero_dim_finite_discrete
    (M := F.tail.carrier)).1
  have hsub : Subsingleton F.tail.carrier :=
    ⟨fun a b => isPreconnected_univ.subsingleton (mem_univ a) (mem_univ b)⟩
  have hne : Nonempty F.tail.carrier := ConnectedSpace.toNonempty
  have hcard : Nat.card F.tail.carrier = 1 := by
    have : Unique F.tail.carrier := uniqueOfSubsingleton (Classical.choice hne)
    exact Nat.card_unique
  unfold diagonalPotentialMass diagonalPotentialMeasure
  rw [h, hcard, Nat.cast_one]

/-- **`tok-volid:point-restricted`**: on a curve, `vol_{X|q}(ξ - t{q}) = 1` for rational
`t ∈ (ν_min, ν_max)`. -/
theorem shiftedRestrictedVolume_eq_one_rat {θ : ClosedRealOneOneForm 1 F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {E : MeteredEffectiveQDivisor 1 F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {t : ℚ} (h₁ : firstValuationMin F θ < t) (h₂ : (t : ℝ) < firstValuationMax F θ) :
    shiftedRestrictedVolume θ E t = 1 := by
  let _ : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  have _ : BorelSpace F.tail.carrier := ⟨rfl⟩
  have hR : shiftedRestrictedVolume θ E t =
      TranscendentalVolumeConcavity.restrictedVolume (firstFlagInclusion F)
        (contMDiff_firstFlagInclusion F) (θ - (t : ℝ) • E.curvature) := by
    unfold shiftedRestrictedVolume firstFlagRestrictedVolume
    rw [← ofRepresentative_sub_smul,
      ← TranscendentalVolumeConcavity.restrictedVolume_eq_classRestrictedVolume]
  rw [hR]
  unfold TranscendentalVolumeConcavity.restrictedVolume
  apply le_antisymm
  · exact iSup₂_le fun φ _ => iSup_le fun hw => (diagonalPotentialMass_point_eq_one hw).le
  · obtain ⟨ψ, hψ, hw⟩ := exists_gentleKahler_restrict hbig hE h₁ h₂
    exact le_iSup₂_of_le ψ hψ (le_iSup_of_le hw (diagonalPotentialMass_point_eq_one hw).ge)

/-- The volume of a nonempty subset of `ℝ⁰` is `1`. -/
theorem volume_nonempty_fin_zero {S : Set (Fin 0 → ℝ)} (hS : S.Nonempty) : volume S = 1 := by
  have : S = univ := by
    obtain ⟨x, hx⟩ := hS
    ext y
    simp only [mem_univ, iff_true]
    have : y = x := Subsingleton.elim y x
    rw [this]; exact hx
  rw [this, volume_pi, Measure.pi_of_empty (fun _ : Fin 0 => (volume : Measure ℝ)),
    measure_univ]

/-- On a curve, `Δ(ξ) ⊆ ℝ` is the interval `[ν_min, ν_max]`, so `vol Δ(ξ) = ν_max - ν_min`. -/
theorem volume_tradOkounkovBody_dimOne {θ : ClosedRealOneOneForm 1 F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    volume (tradOkounkovBody F θ) =
      ENNReal.ofReal (firstValuationMax F θ - firstValuationMin F θ) := by
  set I := Ioo (firstValuationMin F θ) (firstValuationMax F θ) with hI
  have hproj := image_first_tradOkounkovBody_eq_Icc (F := F) hbig
  have hS1 : ∀ t ∈ I, volume (firstCoordinateSlice (tradOkounkovBody F θ) t) = 1 := by
    intro t ht
    apply volume_nonempty_fin_zero
    have : t ∈ (fun x : Fin 1 → ℝ => x 0) '' tradOkounkovBody F θ := by
      rw [hproj]; exact Ioo_subset_Icc_self ht
    obtain ⟨x, hx, hxt⟩ := this
    refine ⟨Fin.tail x, ?_⟩
    show Fin.cons t (Fin.tail x) ∈ tradOkounkovBody F θ
    rw [← hxt, Fin.cons_self_tail]
    exact hx
  rw [volume_eq_lintegral_Ioo_firstCoordinateSlice (isClosed_tradOkounkovBody θ).measurableSet
    hproj.le, setLIntegral_congr_fun measurableSet_Ioo hS1]
  simp

/-- **`tok:A1` from `WNIntegratedStatement F`** (`tok-volid:A1-wn`): on a curve, `vol Δ(ξ) = vol(ξ)` for every
big class, **conditional on Witt Nyström's integrated formula in dimension one**. -/
theorem volumeIdentity_dimOne_of_wn (hWN : WNIntegratedStatement F) : VolumeIdentityStatement F := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  intro α hα
  set θ := Quotient.out α with hθdef
  have hθ : RealBottChern.ofRepresentative θ = α := Quotient.out_eq α
  have hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ) := by rwa [hθ]
  obtain ⟨φ, hφ⟩ := TranscendentalBody.exists_mem_gentleKahlerCurrents_of_isBig hbig
  obtain ⟨E, hE⟩ := exists_isFirstDivisorUnitMetric F hφ.1.1
  set I := Ioo (firstValuationMin F θ) (firstValuationMax F θ) with hI
  have hproj := image_first_tradOkounkovBody_eq_Icc (F := F) hbig
  -- `R = 1` on `(ν_min, ν_max)`
  have hR1 : ∀ t ∈ I, shiftedRestrictedVolume θ E t = 1 := by
    intro t ht
    have hc := continuousOn_restrictedVolume_sub hWN hbig hE
    have h := eq_of_continuousOn_of_rat isOpen_Ioo hc (C := 1) (fun q hq => by
      simp [shiftedRestrictedVolume_eq_one_rat hbig hE hq.1 hq.2]) ht
    rw [← ENNReal.ofReal_toReal (shiftedRestrictedVolume_lt_top θ E t).ne, h, ENNReal.ofReal_one]
  -- the slices are points
  have hS1 : ∀ t ∈ I, volume (firstCoordinateSlice (tradOkounkovBody F θ) t) = 1 := by
    intro t ht
    apply volume_nonempty_fin_zero
    have : t ∈ (fun x : Fin 1 → ℝ => x 0) '' tradOkounkovBody F θ := by
      rw [hproj]; exact Ioo_subset_Icc_self ht
    obtain ⟨x, hx, hxt⟩ := this
    refine ⟨Fin.tail x, ?_⟩
    show Fin.cons t (Fin.tail x) ∈ tradOkounkovBody F θ
    rw [← hxt, Fin.cons_self_tail]
    exact hx
  have hV := sourceClassVolume_eq_lintegral_restrictedVolume (F := F) hWN hbig hE
  have hΔ := volume_eq_lintegral_Ioo_firstCoordinateSlice
    (isClosed_tradOkounkovBody θ).measurableSet hproj.le
  change volume (tradOkounkovBody F θ) = _
  rw [← hθ, hΔ, hV, setLIntegral_congr_fun measurableSet_Ioo hS1,
    setLIntegral_congr_fun measurableSet_Ioo hR1]
  simp

end DimOne

/-! ### The volume identity, given WN in every dimension -/

/-- **`tok:volume-identity`** (DRWNXZ Theorem 7.6 = Theorem 1.1, the book's
`thm:Okounkovtranmain` (1)): `vol Δ_{Y•}(α) = vol(α)/n!` for every flag geometry and every big
class, **conditional on** Witt Nyström's Theorem C in the integrated form (`WNIntegratedStatement F` for
every flag geometry `F`, package WN) and RELGEN's `PushforwardAnalyticStatement`. -/
theorem volumeIdentity_of_wn_of_pushforward
    (hWN : ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 1)), WNIntegratedStatement F)
    (hP : PushforwardAnalyticStatement.{u}) :
    ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 1)), VolumeIdentityStatement F :=
  volumeIdentityAll_of_dimOne (fun m F => hWN (m + 1) F) hP
    (fun F => volumeIdentity_dimOne_of_wn (hWN 0 F))

/-- **`tok:volume-identity`**, with RELGEN's `L²` hypothesis `ModificationL2GenerationStatement`
in place of `PushforwardAnalyticStatement` (through RELGEN's bridge). -/
theorem volumeIdentity_of_wn_of_modificationL2
    (hWN : ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 1)), WNIntegratedStatement F)
    (hM : SGPT.Okounkov.TranscendentalL2.ModificationL2GenerationStatement.{u}) :
    ∀ (m : ℕ) (F : OriginalFlagGeometry.{u} (m + 1)), VolumeIdentityStatement F :=
  volumeIdentity_of_wn_of_pushforward hWN
    (SGPT.Okounkov.TranscendentalL2.pushforwardAnalyticStatement_of_modificationL2Generation hM)

end SGPT.Okounkov.TranscendentalVolId

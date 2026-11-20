import SGPT.Okounkov.TranscendentalVolIdRestrict

/-!
# Restricted volumes bound the slice volumes from above

Package VOL (blueprint `claude-okounkov-transcendental`, node `tok:Bn-implies-Cn`, the density
half; chapter `claude-tok-volid`, node `tok-volid:slice-upper`): Darvas--Reboulet--Witt
Nyström--Xia--Zhang, *Transcendental Okounkov bodies* (DRWNXZ), Lemma 7.5.

Let `X` be a connected compact Kähler manifold of dimension `n = m + 2` with a smooth flag,
`ξ = {θ}` big, `E` a unit metric of `Y₁`, `t ∈ (ν_min, ν_max)` rational, `ξ_t = ξ - t{Y₁}` and
`Δ_t(ξ) = {y : (t, y) ∈ Δ(ξ)}`. Assuming `B_{n-1}` (`PartialVolumeIdentityStatement m`, on the
flag geometry `Y₁ ⊇ ⋯ ⊇ Yₙ` of dimension `m + 1`):

`(n - 1)! vol Δ_t(ξ) ≤ vol_{X|Y₁}(ξ_t)` (`volume_slice_le`).

Proof (DRWNXZ): enumerate `ν(Ω_t) = {ν(T_k)}` (countable, `tok:valuation-analytic`), let
`G_k = T_k - t[Y₁]` (Kähler, analytic, finite on `Y₁`) and choose inductively `R_k ∈ Ω(ξ_t)` less
singular than `R_{k-1}` and `G_k` (`tok:sing-decrease`). The restrictions `R_k|_{Y₁}` are Kähler
currents in `𝒜ᵍ(Y₁, ξ_t|_{Y₁})`; by `B_{n-1}` the partial bodies `Δ_k = Δ(ξ_t|_{Y₁}; R_k|_{Y₁})`
have volume `(1/(n-1)!) ∫_{Y₁} ⟨(R_k|_{Y₁})^{n-1}⟩ ≤ vol_{X|Y₁}(ξ_t)/(n-1)!`; they increase,
contain the tail valuations `ν(G_k|_{Y₁})` (`tok:partial-analytic`), so their union is dense in
`Δ_t(ξ)` (`tok:slice-density`), and the volume of the closure of an increasing union of convex
sets is the limit of the volumes.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalVolId

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalSlice
open SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalWN
open SGPT.Okounkov.TranscendentalPartial
open SGPT.PSH SGPT.PSH.VariableComplexAtlas

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 2)}

/-- `R(t)` is the restricted volume of the representative `θ - tΘ_E`. -/
theorem shiftedRestrictedVolume_eq (θ : ClosedRealOneOneForm (m + 2) F.carrier)
    (E : MeteredEffectiveQDivisor (m + 2) F.carrier) (t : ℝ) :
    shiftedRestrictedVolume θ E t =
      (letI : MeasurableSpace F.tail.carrier := borel F.tail.carrier
       haveI : BorelSpace F.tail.carrier := ⟨rfl⟩
       TranscendentalVolumeConcavity.restrictedVolume (firstFlagInclusion F)
        (contMDiff_firstFlagInclusion F) (θ - t • E.curvature)) := by
  let _ : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  have _ : BorelSpace F.tail.carrier := ⟨rfl⟩
  unfold shiftedRestrictedVolume firstFlagRestrictedVolume
  rw [← ofRepresentative_sub_smul, ← TranscendentalVolumeConcavity.restrictedVolume_eq_classRestrictedVolume]

/-- A term of the restricted volume. -/
theorem diagonalPotentialMass_restrict_le (θ : ClosedRealOneOneForm (m + 2) F.carrier)
    (E : MeteredEffectiveQDivisor (m + 2) F.carrier) (t : ℝ) {R : F.carrier → EReal}
    (hR : R ∈ gentleKahlerCurrents (θ - t • E.curvature))
    (hw : IsThetaPshPotential (firstFlagRestriction F (θ - t • E.curvature)).val
      (restrictFirst F R)) :
    (letI : MeasurableSpace F.tail.carrier := borel F.tail.carrier
     haveI : BorelSpace F.tail.carrier := ⟨rfl⟩
     diagonalPotentialMass (firstFlagRestriction F (θ - t • E.curvature)) (restrictFirst F R) hw) ≤
      shiftedRestrictedVolume θ E t := by
  let _ : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  have _ : BorelSpace F.tail.carrier := ⟨rfl⟩
  rw [shiftedRestrictedVolume_eq]
  unfold TranscendentalVolumeConcavity.restrictedVolume
  exact le_iSup₂_of_le R hR (le_iSup_of_le hw le_rfl)

/-- **`tok:Bn-implies-Cn`, upper bound** (DRWNXZ Lemma 7.5, density half): assuming `B_{n-1}`,
`(n - 1)! vol Δ_t(ξ) ≤ vol_{X|Y₁}(ξ - t{Y₁})` for rational `t ∈ (ν_min, ν_max)`. -/
theorem volume_slice_le (hB : PartialVolumeIdentityStatement.{u} m)
    {θ : ClosedRealOneOneForm (m + 2) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {E : MeteredEffectiveQDivisor (m + 2) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {t : ℚ} (h₁ : firstValuationMin F θ < t) (h₂ : (t : ℝ) < firstValuationMax F θ) :
    ((m + 1).factorial : ℝ≥0∞) * volume (firstCoordinateSlice (tradOkounkovBody F θ) t) ≤
      shiftedRestrictedVolume θ E t := by
  let _ : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  have _ : BorelSpace F.tail.carrier := ⟨rfl⟩
  set θt := θ - (t : ℝ) • E.curvature with hθt
  set θr := firstFlagRestriction F θt with hθr
  set Ωt := {φ ∈ gentleKahlerCurrents θ | flagValuation F φ 0 = t} with hΩt
  have hslice := (slice_eq_closure_fixedFirst hbig h₁ h₂).1
  -- the empty case
  by_cases hne : (flagValuation F '' Ωt).Nonempty
  swap
  · have hempty : firstCoordinateSlice (tradOkounkovBody F θ) t = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun y hy => ?_
      have hmem : (Fin.cons (t : ℝ) y : Fin (m + 2) → ℝ) ∈
          {x ∈ tradOkounkovBody F θ | x 0 = t} := ⟨hy, by simp⟩
      rw [hslice, not_nonempty_iff_eq_empty.mp hne, closure_empty] at hmem
      exact hmem
    rw [hempty, measure_empty, mul_zero]
    exact bot_le
  -- enumerate the valuations of `Ω_t`
  have hcount : (flagValuation F '' Ωt).Countable :=
    (countable_image_gentleKahlerCurrents (F := F) θ).mono (image_mono fun φ hφ => hφ.1)
  obtain ⟨f, hf⟩ := hcount.exists_eq_range hne
  have hfmem : ∀ k, ∃ φ ∈ Ωt, flagValuation F φ = f k := fun k => by
    have : f k ∈ range f := mem_range_self k
    rw [← hf] at this
    exact this
  choose φ hφ hφf using hfmem
  -- the residuals `G_k = T_k - t[Y₁]`
  have hres := fun k => exists_residual_of_fixedFirst hE (hφ k).1 (hφ k).2
  choose v hvK hvA hwA hwK hνv using hres
  -- the dominating currents `R_k ∈ Ω(ξ_t)`
  have hstep : ∀ (ψ : F.carrier → EReal), IsKahlerCurrentPotential θt ψ → ∀ k : ℕ,
      ∃ ψ' ∈ gentleKahlerCurrents θt, SingularityLE ψ ψ' ∧ SingularityLE (v k) ψ' :=
    fun ψ hψ k => TranscendentalBody.exists_mem_gentleKahlerCurrents_singularityLE hψ (hvK k)
  choose S hS hS₁ hS₂ using hstep
  let R : ℕ → {ψ // ψ ∈ gentleKahlerCurrents θt} := fun k =>
    Nat.rec (motive := fun _ => {ψ // ψ ∈ gentleKahlerCurrents θt})
      ⟨S (v 0) (hvK 0) 0, hS _ _ 0⟩
      (fun k Rk => ⟨S Rk.1 Rk.2.2 (k + 1), hS _ _ (k + 1)⟩) k
  have hR0 : (R 0).1 = S (v 0) (hvK 0) 0 := rfl
  have hRs : ∀ k, (R (k + 1)).1 = S (R k).1 (R k).2.2 (k + 1) := fun k => rfl
  have hRmono : ∀ k, SingularityLE (R k).1 (R (k + 1)).1 := fun k => by
    rw [hRs]; exact hS₁ _ _ _
  have hvR : ∀ k, SingularityLE (v k) (R k).1 := by
    intro k
    cases k with
    | zero => rw [hR0]; exact hS₂ _ _ 0
    | succ k => rw [hRs]; exact hS₂ _ _ (k + 1)
  have hRmono' : ∀ j k, j ≤ k → SingularityLE (R j).1 (R k).1 := by
    intro j k hjk
    induction k, hjk using Nat.le_induction with
    | base => exact singularityLE_refl _
    | succ k _ ih => exact singularityLE_trans ih (hRmono k)
  -- restrictions to `Y₁`
  have hrestrictLE : ∀ {a b : F.carrier → EReal}, SingularityLE a b →
      SingularityLE (restrictFirst F a) (restrictFirst F b) := by
    rintro a b ⟨C, hC⟩
    exact ⟨C, fun y _ => hC _ (mem_univ _)⟩
  have hwR : ∀ k, SingularityLE (restrictFirst F (v k)) (restrictFirst F (R k).1) :=
    fun k => hrestrictLE (hvR k)
  have hrK : ∀ k, IsKahlerCurrentPotential θr (restrictFirst F (R k).1) := fun k => by
    obtain ⟨κ, hκ⟩ := (R k).2.2
    exact isKahlerCurrentPotential_restrict hκ (hwA k).1.2 (hwR k)
  have hrpsh : ∀ k, IsThetaPshPotential θr.val (restrictFirst F (R k).1) := fun k =>
    isThetaPshPotential_restrict (R k).2.1.1.1 (hwA k).1.2 (hwR k)
  have hrglob : ∀ k, restrictFirst F (R k).1 ∈ globalAnalyticCurrents θr := fun k =>
    ⟨hrpsh k, restrict_hasAnalyticSingularities
      (gentleKahlerCurrents_subset_globalAnalyticCurrents (R k).2).2⟩
  -- the partial bodies on `Y₁`
  set P : ℕ → Set (Fin (m + 1) → ℝ) := fun k =>
    partialOkounkovBody F.tail θr (restrictFirst F (R k).1) with hP
  have hPmono : Monotone P := by
    intro j k hjk
    exact partialOkounkovBody_mono θr (hrestrictLE (hRmono' j k hjk))
  have hPconv : ∀ k, Convex ℝ (P k) := fun k => convex_partialOkounkovBody θr _
  have hPvol : ∀ k, ((m + 1).factorial : ℝ≥0∞) * volume (P k) ≤ shiftedRestrictedVolume θ E t := by
    intro k
    have hBk := hB F.tail θr (restrictFirst F (R k).1) (hrglob k) (hrK k)
    have hle := diagonalPotentialMass_restrict_le θ E t (R k).2 (hrpsh k)
    change volume (P k) = _ at hBk
    rw [hBk, ENNReal.mul_div_cancel]
    · exact hle
    · exact_mod_cast (Nat.factorial_pos (m + 1)).ne'
    · exact ENNReal.natCast_ne_top _
  -- the tail valuations lie in the partial bodies
  have htail : ∀ k, (fun i : Fin (m + 1) => f k i.succ) ∈ P k := by
    intro k
    have hval : (fun i : Fin (m + 1) => f k i.succ) = flagValuation F.tail (restrictFirst F (v k)) := by
      rw [← hφf k, hνv k]
      funext i
      simp
    rw [hval]
    exact flagValuation_mem_partialOkounkovBody_of_analytic (hrK k)
      (globalAnalyticCurrents_subset_analyticCurrents θr (hrglob k)) ⟨hwA k, hwR k⟩
  -- the slice lies in the closure of the union
  have hsub : firstCoordinateSlice (tradOkounkovBody F θ) t ⊆ closure (⋃ k, P k) := by
    intro y hy
    have hmem : (Fin.cons (t : ℝ) y : Fin (m + 2) → ℝ) ∈
        {x ∈ tradOkounkovBody F θ | x 0 = t} := ⟨hy, by simp⟩
    rw [hslice, hf] at hmem
    have hcont : Continuous fun x : Fin (m + 2) → ℝ => fun i : Fin (m + 1) => x i.succ := by
      fun_prop
    have h := image_closure_subset_closure_image hcont (mem_image_of_mem _ hmem)
    have hy' : (fun i : Fin (m + 1) => (Fin.cons (t : ℝ) y : Fin (m + 2) → ℝ) i.succ) = y := by
      funext i; simp
    rw [hy'] at h
    refine closure_mono ?_ h
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact mem_iUnion.mpr ⟨k, htail k⟩
  have hU : Convex ℝ (⋃ k, P k) := Directed.convex_iUnion hPmono.directed_le hPconv
  calc ((m + 1).factorial : ℝ≥0∞) * volume (firstCoordinateSlice (tradOkounkovBody F θ) t)
      ≤ ((m + 1).factorial : ℝ≥0∞) * volume (closure (⋃ k, P k)) := by gcongr
    _ = ((m + 1).factorial : ℝ≥0∞) * ⨆ k, volume (P k) := by
        rw [volume_closure_of_convex hU, hPmono.measure_iUnion]
    _ = ⨆ k, ((m + 1).factorial : ℝ≥0∞) * volume (P k) := ENNReal.mul_iSup _ _
    _ ≤ shiftedRestrictedVolume θ E t := iSup_le hPvol

end SGPT.Okounkov.TranscendentalVolId

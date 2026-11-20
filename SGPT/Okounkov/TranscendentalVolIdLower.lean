import SGPT.Okounkov.TranscendentalVolIdUpper
import SGPT.Okounkov.TranscendentalVolIdDivisorRestrict
import SGPT.Okounkov.TranscendentalVolIdLinear
import SGPT.Okounkov.TranscendentalPartialBirational
import SGPT.Okounkov.TranscendentalBodyKahlerLimit
import SGPT.Okounkov.TranscendentalLiftingBlowupKahler
import SGPT.Okounkov.TranscendentalLiftingApprox
import SGPT.Okounkov.TranscendentalCoreRepresentative
import SGPT.Foundations.Analysis.Pending.ModificationMassInvariance
import SGPT.Foundations.Analysis.Pending.AnalyticModificationMixedMass
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple

/-!
# Restricted volumes bound the slice volumes from below

Package VOL (blueprint `claude-okounkov-transcendental`, node `tok:Bn-implies-Cn`, inclusion
half; chapter `claude-tok-volid`, nodes `tok-volid:slice-lower`, `tok-volid:kahler-slice-zero`,
`tok-volid:shift-body`, `tok-volid:restricted-mass`): Darvas--Reboulet--Witt Nyström--Xia--Zhang,
*Transcendental Okounkov bodies* (DRWNXZ), Lemma 7.5.

Let `X` be a connected compact Kähler manifold of dimension `n = m + 2` with a smooth flag,
`ξ = {θ}` big, `E` a unit metric of `Y₁`, `t ∈ (ν_min, ν_max)` rational, `ξ_t = ξ - t{Y₁}`.
Assuming `A_{n-1}` (`VolumeIdentityAllStatement m`, for all flag geometries of dimension
`m + 1`) and `PushforwardAnalyticStatement` (RELGEN, through `tok:partial-birational`):

`vol_{X|Y₁}(ξ_t) ≤ (n - 1)! vol Δ_t(ξ)` (`restrictedVolume_le_volume_slice`).

Route (an adaptation of DRWNXZ's proof, which pulls back, subtracts, extends and pushes forward
each current of the partial body on `Y₁`): fix `R ∈ Ω(ξ_t)` finite at a point of `Y₁`, with
resolution data `π^*R = [D] + R'` along a lifting `(W•, g)` (`tok:resolution-lifting`). Then

1. `Δ(ξ_t; R) g = ν_W(D) + Δ_W({R'})` (`tok:partial-birational`, needs `PushforwardAnalytic`),
   and `ν_W(D)` has first coordinate `0` (`W₁` is not contained in `Supp D`);
2. `{0} × Δ_{W₁}({R'}|_{W₁}) ⊆ Δ_W({R'})` (`cons_zero_mem_tradOkounkovBody`): `{R'} + ε{ω}` is a
   Kähler class (`R'` has bounded potentials, `lma:logsingrem`), for which the slice at `0`
   contains the body of the restricted class (`tok:ct-gentle` through SLICE's
   `cons_mem_tradOkounkovBody_of_extension`), and `Δ_W({R'}) = ⋂_ε Δ_W({R'} + ε{ω})`
   (`tok:kahler-limit`);
3. `Δ(ξ_t) + t e₁ ⊆ Δ(ξ)` (`add_smul_single_mem_tradOkounkovBody`, adding `t[Y₁]`);
4. the correction matrix `g` fixes the first coordinate and has determinant `1`, so
   `y ↦ tail((ν_W(D) + (0, y)) g⁻¹)` maps `Δ_{W₁}({R'}|_{W₁})` into `Δ_t(ξ)` preserving volume;
5. `A_{n-1}` on the tail `W₁ ⊇ W₂ ⊇ ⋯` of the lifted flag: `vol Δ_{W₁}({R'}|_{W₁}) =
   vol({R'}|_{W₁})/(n-1)!`, and `vol({R'}|_{W₁}) = ∫_{W₁} ⟨(R'|_{W₁})^{n-1}⟩` (bounded potentials)
   `= ∫_{Y₁} ⟨(R|_{Y₁})^{n-1}⟩` (`restrictedResidual_mass_eq`: the restriction of `[D]` is a
   divisor on `W₁` charging no non-pluripolar mass, and `π|_{W₁} : W₁ → Y₁` is a modification).

Taking the supremum over `R` gives the restricted volume. Compared with DRWNXZ, the partial
bodies on `Y₁` and the pushforward step of `tok:approx-pushforward` are replaced by the
already proved `tok:partial-birational` and the mass identity of step 5.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalVolId

open Set Filter MeasureTheory Matrix
open scoped ENNReal NNReal Topology Manifold ContDiff Pointwise
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalSlice
open SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalWN
open SGPT.Okounkov.TranscendentalPartial SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.TranscendentalRelGen
open SGPT.PSH SGPT.PSH.VariableComplexAtlas

/-! ### Bigness and adding `t[Y₁]` -/

section Shift

variable {n : ℕ} {G : OriginalFlagGeometry.{u} n}

/-- A class with a gentle Kähler current is big. -/
theorem isBig_of_gentleKahlerCurrents_nonempty {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (n + 1)) X] [IsComplexManifold (n + 1) X] [CompactSpace X]
    {θ : ClosedRealOneOneForm (n + 1) X} (h : (gentleKahlerCurrents θ).Nonempty) :
    SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ) := by
  obtain ⟨ψ, hψ⟩ := h
  obtain ⟨κ, hκ⟩ := hψ.2
  rw [SGPT.PSH.BookCurrent.isBig_iff_isBigClass]
  exact ⟨⟨θ, rfl, ψ, κ, hκ⟩⟩

end Shift

section AddDivisor

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- **`tok-volid:shift-body`**: adding `t[Y₁]` (`t ∈ ℚ_{≥0}`) maps `Δ(ξ - t{Y₁})` into `Δ(ξ)`:
`Δ(ξ_t) + t e₁ ⊆ Δ(ξ)`. -/
theorem add_smul_single_mem_tradOkounkovBody {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {t : ℚ} (ht : 0 ≤ t)
    (hbigt : SGPT.PSH.BookCurrent.IsBig
      (RealBottChern.ofRepresentative (θ - (t : ℝ) • E.curvature)))
    {z : Fin (m + 1) → ℝ} (hz : z ∈ tradOkounkovBody F (θ - (t : ℝ) • E.curvature)) :
    z + (t : ℝ) • (Fin.cons 1 0 : Fin (m + 1) → ℝ) ∈ tradOkounkovBody F θ := by
  set T : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) :=
    fun x => x + (t : ℝ) • (Fin.cons 1 0 : Fin (m + 1) → ℝ) with hT
  have hTc : Continuous T := by fun_prop
  rw [SGPT.Okounkov.TranscendentalDensity.tradOkounkovBody_eq_closure_gentleKahlerCurrents hbigt]
    at hz
  have hsub : flagValuation F '' gentleKahlerCurrents (θ - (t : ℝ) • E.curvature) ⊆
      T ⁻¹' tradOkounkovBody F θ := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hφA : φ ∈ analyticCurrents (θ - (t : ℝ) • E.curvature) :=
      gentleCurrents_subset_analyticCurrents _ hφ.1
    have hΦ := add_smul_mem_analyticCurrents hφA (weight_mem_analyticCurrents hE)
      (a := 1) (b := t) zero_le_one ht
    simp only [Rat.cast_one, one_smul, sub_add_cancel, EReal.coe_one, one_mul] at hΦ
    have hν := flagValuation_add_smul (F := F) hφA.1 (weight_mem_analyticCurrents hE).1
      (a := (1 : ℝ)) (b := (t : ℝ)) zero_le_one (by exact_mod_cast ht)
    rw [flagValuation_weight hE] at hν
    simp only [EReal.coe_one, one_mul, one_smul] at hν
    have hΩθ := TranscendentalBody.exists_mem_gentleKahlerCurrents_of_isBig hbig
    have hmem := SGPT.Okounkov.TranscendentalDensity.densityStatement (m + 1) F θ hΩθ _ hΦ
    rw [← SGPT.Okounkov.TranscendentalDensity.tradOkounkovBody_eq_closure_gentleKahlerCurrents hbig,
      hν] at hmem
    exact hmem
  have h := closure_mono hsub hz
  rw [(IsClosed.preimage hTc (isClosed_tradOkounkovBody θ)).closure_eq] at h
  exact h

end AddDivisor

/-! ### The slice at `0` of the body of a class with a bounded positive current -/

section KahlerSlice

/-- `(a + b)|_{Y₁} = a|_{Y₁} + b|_{Y₁}`. -/
theorem firstFlagRestriction_add {m : ℕ} (W : OriginalFlagGeometry.{u} (m + 1))
    (a b : ClosedRealOneOneForm (m + 1) W.carrier) :
    firstFlagRestriction W (a + b) = firstFlagRestriction W a + firstFlagRestriction W b :=
  SGPT.Okounkov.TranscendentalBody.pullback_add' _ a b

variable {m : ℕ} {W : OriginalFlagGeometry.{u} (m + 2)}

/-- A first-divisor unit metric exists. -/
theorem exists_isFirstDivisorUnitMetric {k : ℕ} (W : OriginalFlagGeometry.{u} (k + 1))
    {θ : ClosedRealOneOneForm (k + 1) W.carrier} {u : W.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    ∃ E : MeteredEffectiveQDivisor (k + 1) W.carrier, IsFirstDivisorUnitMetric W E := by
  obtain ⟨D, hDI, E, hEW, hmetric, -, -⟩ :=
    SGPT.Okounkov.exists_normalized_smooth_divisor_residual_generic_zero hu W.firstDivisor
  exact ⟨E, D, hDI, hEW, hmetric⟩

/-- **`tok-volid:kahler-slice-zero`**: if `β` is big and carries a bounded `β`-psh potential, then
`{0} × Δ_{W₁}(β|_{W₁}) ⊆ Δ_W(β)`. -/
theorem cons_zero_mem_tradOkounkovBody {β : ClosedRealOneOneForm (m + 2) W.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative β))
    {b : W.carrier → EReal} (hb : IsThetaPshPotential β.val b) {C : ℝ}
    (hbC : ∀ y, ((-C : ℝ) : EReal) ≤ b y ∧ b y ≤ (C : EReal))
    {y : Fin (m + 1) → ℝ} (hy : y ∈ tradOkounkovBody W.tail (firstFlagRestriction W β)) :
    (Fin.cons 0 y : Fin (m + 2) → ℝ) ∈ tradOkounkovBody W β := by
  obtain ⟨EW, hEW⟩ := exists_isFirstDivisorUnitMetric W hb
  rw [TranscendentalBody.tradOkounkovBody_eq_iInter_add_kahler hbig]
  refine mem_iInter₂.mpr fun ε hε => ?_
  have hε' : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hε2 : (0 : ℝ) < (ε : ℝ) / 2 := by linarith
  set w₀ := W.omega
  -- a Kähler form in `{β} + ε{ω}`
  set D₀ := MeteredDivisorScaling.smul (le_refl (0 : ℚ)) EW with hD₀
  have hD₀w : ∀ x, D₀.weight x = 0 := fun x => by simp [hD₀]
  have hD₀c : D₀.curvature = 0 := by simp [hD₀]
  have hbfin : ∀ x, b x = ((b x).toReal : EReal) := fun x => by
    have h1 : b x ≠ ⊥ := fun h => by
      have := (hbC x).1; rw [h] at this; exact EReal.coe_ne_bot _ (le_bot_iff.mp this)
    have h2 : b x ≠ ⊤ := fun h => by
      have := (hbC x).2; rw [h] at this; exact EReal.coe_ne_top _ (top_le_iff.mp this)
    exact (EReal.coe_toReal h2 h1).symm
  let L : ResidualNefReduction.HasLogSingularitiesAlong D₀ b :=
    { residual := fun x => (b x).toReal
      bound := C
      residual_bound := fun x => by
        have h1 := (hbC x).1
        have h2 := (hbC x).2
        rw [hbfin x] at h1 h2
        rw [abs_le]
        exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
      weight_add := fun x => by rw [hD₀w, zero_add]; exact hbfin x }
  have hK : IsKahlerCurrentPotential (β + (ε : ℝ) • w₀.form) b := by
    refine ⟨KahlerBackground.smul hε' w₀, ?_⟩
    rw [KahlerBackground.smul_form, add_sub_cancel_right]
    exact hb
  obtain ⟨h, hh, hKah⟩ := exists_kahlerForm_of_logSingularities hK L
  rw [hD₀c, sub_zero] at hKah
  let κ : KahlerBackground (m + 2) W.carrier :=
    ⟨(β + (ε : ℝ) • w₀.form) + ManifoldTubePositivity.ddcClosedForm h hh, hKah⟩
  have hκclass : RealBottChern.ofRepresentative κ.form =
      RealBottChern.ofRepresentative (β + (ε : ℝ) • w₀.form) := ofRepresentative_add_ddc _ hh
  -- the slice at `0` of `Δ(κ)` contains `Δ(κ|_{W₁})`
  have hΩ : (gentleKahlerCurrents (κ.form + ((0 : ℚ) : ℝ) • EW.curvature)).Nonempty := by
    simpa using gentleKahlerCurrents_nonempty_of_kahler κ
  have hcons : ∀ w ∈ gentleKahlerCurrents (firstFlagRestriction W κ.form),
      (Fin.cons 0 (flagValuation W.tail w) : Fin (m + 2) → ℝ) ∈
        tradOkounkovBody W (β + (ε : ℝ) • w₀.form) := by
    intro w hw
    have h := cons_mem_tradOkounkovBody_of_extension κ hEW (le_refl (0 : ℚ)) hΩ hw
    simp only [Rat.cast_zero, zero_smul, add_zero] at h
    rwa [tradOkounkovBody_eq_of_class_eq hκclass] at h
  have hΩr : (gentleKahlerCurrents (firstFlagRestriction W κ.form)).Nonempty := by
    have := gentleKahlerCurrents_nonempty_of_kahler (restrictedKahlerForm κ)
    rwa [restrictedKahlerForm_form] at this
  have hbody : (fun y : Fin (m + 1) → ℝ => (Fin.cons 0 y : Fin (m + 2) → ℝ)) ''
      tradOkounkovBody W.tail (firstFlagRestriction W κ.form) ⊆
        tradOkounkovBody W (β + (ε : ℝ) • w₀.form) := by
    rw [SGPT.Okounkov.TranscendentalDensity.tradOkounkovBody_eq_closure_gentleKahlerCurrents
      (isBig_of_gentleKahlerCurrents_nonempty hΩr)]
    refine (image_closure_subset_closure_image (by fun_prop)).trans ?_
    refine closure_minimal ?_ (isClosed_tradOkounkovBody _)
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact hcons w hw
  -- `Δ(β|_{W₁}) ⊆ Δ(κ|_{W₁})`
  set κ₂ := restrictedKahlerForm (KahlerBackground.smul hε2 w₀) with hκ₂
  have hsub : tradOkounkovBody W.tail (firstFlagRestriction W β) ⊆
      tradOkounkovBody W.tail (firstFlagRestriction W β + (κ₂.form + κ₂.form)) :=
    TranscendentalBody.tradOkounkovBody_subset_add _ (κ := κ₂)
      (by rw [add_sub_cancel_right]; exact κ₂.isSemipositive)
  have hform : firstFlagRestriction W β + (κ₂.form + κ₂.form) =
      firstFlagRestriction W (β + (ε : ℝ) • w₀.form) := by
    rw [hκ₂, restrictedKahlerForm_form, KahlerBackground.smul_form, ← firstFlagRestriction_add,
      ← firstFlagRestriction_add, ← add_smul, add_halves]
  have hclass : RealBottChern.ofRepresentative (firstFlagRestriction W (β + (ε : ℝ) • w₀.form)) =
      RealBottChern.ofRepresentative (firstFlagRestriction W κ.form) :=
    firstFlagRestriction_class_congr W hκclass.symm
  rw [hform, tradOkounkovBody_eq_of_class_eq hclass] at hsub
  exact hbody ⟨y, hsub hy, rfl⟩

end KahlerSlice

end SGPT.Okounkov.TranscendentalVolId

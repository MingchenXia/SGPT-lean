import SGPT.Okounkov.TranscendentalL2Corollaries
import SGPT.Okounkov.TranscendentalBodyKahlerLimit
import SGPT.Okounkov.TranscendentalBodySingDecrease

/-!
# Partial Okounkov bodies: monotonicity and limits in the class

Blueprint chapter `claude-pob` (nodes `claude-pob:mono-form`, `claude-pob:add-limit`,
`claude-pob:scaling-limit`); the analytic input of the book's `def:POBKahcurr`,
`lma:Okounkov:L1517`, `cor:Kahlercurrentcase`, `lma:Okomonotone` and `thm:pobmain` (chapter
*The theory of Okounkov bodies*, section *Transcendental partial Okounkov bodies*).

For a Kähler current `R = θ + dd^c ψ` with analytic singularities of a global type
(`ψ ∈ 𝒜ᵍ(θ)`), `Δ(θ; ψ) = closure ν(Ω(θ; ψ))` is the DRWNXZ partial body
(`TranscendentalPartial.partialOkounkovBody`), which is the book's body of `def:POBanalsing`
(`TranscendentalL2.analyticPartialBody_eq_partialOkounkovBody`).

* `partialOkounkovBody_subset_of_le`, `tradOkounkovBody_subset_of_le`: the bodies increase when
  a semipositive form is added to the background (`Ω(θ; ψ) ⊆ Ω(θ + γ; ψ)`).
* `partialOkounkovBody_eq_iInter_add` (**limit in the class**): for `γ ≥ 0`,
  `Δ(θ; ψ) = ⋂_{ε ∈ ℚ_{>0}} Δ(θ + ε γ; ψ)`. Proof: resolution data `π^*R = [D] + R'`
  (`exists_resolutionData`) are resolution data for `θ + εγ` as well, so
  `Δ(θ + εγ; ψ) g ⊆ ν([D]) + Δ_W({R'} + ε π^*{γ}) ⊆ ν([D]) + Δ_W({R'} + ε C {ω_W})`
  (`TranscendentalPartial.image_partialOkounkovBody_subset`); the intersection of the right-hand
  sides is `ν([D]) + Δ_W({R'})` (`TranscendentalBody.tradOkounkovBody_eq_iInter_add_kahler`, the
  Kähler limit of `thm:Okounkovtranmain` (4)), which is `Δ(θ; ψ) g` by DRWNXZ Lemma 5.5
  (`TranscendentalL2.partialOkounkovBody_birational`, unconditional).
* `partialOkounkovBody_smul_subset`: `Δ(θ; q ψ) ⊆ q Δ(q⁻¹ θ; ψ)` (`q ∈ ℚ_{>0}`).
* `mem_partialOkounkovBody_of_forall_smul` (**limit under scaling**, the step
  `⋂_ε Δ(θ, (1 - ε) φ_j) = Δ(θ, φ_j)` of the book's proof of `lma:Okounkov:L1517`): if
  `x ∈ Δ(θ; (1 - a) ψ)` for all rational `a ∈ (0, 1)`, then `x ∈ Δ(θ; ψ)`. The book compares
  volumes (with `eq:volpobanaly`, i.e. `thm:Okounkovtranmain` (1)); here
  `(1 - a)⁻¹ x ∈ Δ((1 - a)⁻¹ θ; ψ) ⊆ Δ(θ + ε ω; ψ)` for small `a`, so `x ∈ Δ(θ + εω; ψ)` for all
  `ε`, and the limit in the class applies: **no volume identity is needed**.
* `mem_partialOkounkovBody_of_forall_singularityLE`: the form used with `prop:compqequi`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.PartialBody

open Set Filter
open scoped Pointwise Topology Matrix
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.TranscendentalPartial

/-! ### Monotonicity in the background form -/

section Monotone

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A Kähler current stays a Kähler current when a semipositive form is added to the
background. -/
theorem isKahlerCurrentPotential_of_le {θ θ' : ClosedRealOneOneForm n M} {φ : M → EReal}
    (hφ : IsKahlerCurrentPotential θ φ) (h : (θ' - θ).val.IsSemipositive) :
    IsKahlerCurrentPotential θ' φ := by
  obtain ⟨κ, hκ⟩ := hφ
  refine ⟨κ, TranscendentalBody.isThetaPshPotential_of_le hκ ?_⟩
  have heq : θ' - κ.form - (θ - κ.form) = θ' - θ := by abel
  rwa [heq]

/-- `𝒢(θ) ⊆ 𝒢(θ')` for `θ ≤ θ'`. -/
theorem gentleCurrents_subset_of_le {θ θ' : ClosedRealOneOneForm n M}
    (h : (θ' - θ).val.IsSemipositive) : gentleCurrents θ ⊆ gentleCurrents θ' :=
  fun _ hφ => ⟨TranscendentalBody.isThetaPshPotential_of_le hφ.1 h, hφ.2⟩

/-- `Ω(θ) ⊆ Ω(θ')` for `θ ≤ θ'`. -/
theorem gentleKahlerCurrents_subset_of_le {θ θ' : ClosedRealOneOneForm n M}
    (h : (θ' - θ).val.IsSemipositive) : gentleKahlerCurrents θ ⊆ gentleKahlerCurrents θ' :=
  fun _ hφ => ⟨gentleCurrents_subset_of_le h hφ.1, isKahlerCurrentPotential_of_le hφ.2 h⟩

/-- `Ω(θ; ψ) ⊆ Ω(θ'; ψ)` for `θ ≤ θ'`. -/
theorem gentleKahlerCurrentsBelow_subset_of_le {θ θ' : ClosedRealOneOneForm n M}
    (h : (θ' - θ).val.IsSemipositive) (ψ : M → EReal) :
    gentleKahlerCurrentsBelow θ ψ ⊆ gentleKahlerCurrentsBelow θ' ψ :=
  fun _ hφ => ⟨gentleKahlerCurrents_subset_of_le h hφ.1, hφ.2⟩

end Monotone

section Flag

variable {n : ℕ} {F : OriginalFlagGeometry.{u} n}

/-- `Δ(θ) ⊆ Δ(θ')` for `θ ≤ θ'`. -/
theorem tradOkounkovBody_subset_of_le {θ θ' : ClosedRealOneOneForm n F.carrier}
    (h : (θ' - θ).val.IsSemipositive) : tradOkounkovBody F θ ⊆ tradOkounkovBody F θ' := by
  rw [tradOkounkovBody_eq_closure_image, tradOkounkovBody_eq_closure_image]
  exact closure_mono (image_mono (gentleCurrents_subset_of_le h))

/-- **`claude-pob:mono-form`**: `Δ(θ; ψ) ⊆ Δ(θ'; ψ)` for `θ ≤ θ'`. -/
theorem partialOkounkovBody_subset_of_le {θ θ' : ClosedRealOneOneForm n F.carrier}
    (h : (θ' - θ).val.IsSemipositive) (ψ : F.carrier → EReal) :
    partialOkounkovBody F θ ψ ⊆ partialOkounkovBody F θ' ψ :=
  closure_mono (image_mono (gentleKahlerCurrentsBelow_subset_of_le h ψ))

end Flag

/-! ### Resolution data and the limit in the class -/

section Limit

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- Resolution data of `θ + dd^c ψ` are resolution data of `θ' + dd^c ψ` for `θ ≤ θ'`. -/
theorem isResolutionData_of_le {θ θ' : ClosedRealOneOneForm (m + 1) F.carrier}
    {ψ : F.carrier → EReal} {W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    {hπ : IsFlagLifting F W π} {D : MeteredEffectiveQDivisor (m + 1) W.carrier}
    {b : W.carrier → EReal} (hR : IsResolutionData θ ψ hπ D b)
    (h : (θ' - θ).val.IsSemipositive) : IsResolutionData θ' ψ hπ D b where
  psh := by
    refine TranscendentalBody.isThetaPshPotential_of_le hR.psh ?_
    have heq : ClosedRealOneOneForm.pullback hπ.1.1 θ' - D.curvature -
        (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature) =
          ClosedRealOneOneForm.pullback hπ.1.1 (θ' - θ) := by
      rw [TranscendentalBody.pullback_sub']
      abel
    rw [heq]
    exact ClosedRealOneOneForm.pullback_isSemipositive hπ.1.1 h
  bounded := hR.bounded
  eq := hR.eq

/-- **`claude-pob:add-limit`** (limit of partial bodies in the class): for a Kähler current
`θ + dd^c ψ`, `ψ ∈ 𝒜ᵍ(θ)`, and a semipositive form `γ`,
`Δ(θ; ψ) = ⋂_{ε ∈ ℚ_{>0}} Δ(θ + ε γ; ψ)`. -/
theorem partialOkounkovBody_eq_iInter_add {θ γ : ClosedRealOneOneForm (m + 1) F.carrier}
    {ψ : F.carrier → EReal} (hψ : ψ ∈ globalAnalyticCurrents θ)
    (hK : IsKahlerCurrentPotential θ ψ) (hγ : γ.val.IsSemipositive) :
    partialOkounkovBody F θ ψ =
      ⋂ (ε : ℚ) (_ : 0 < ε), partialOkounkovBody F (θ + (ε : ℝ) • γ) ψ := by
  apply Subset.antisymm
  · refine subset_iInter₂ fun ε hε => partialOkounkovBody_subset_of_le ?_ ψ
    rw [add_sub_cancel_left]
    exact KahlerDomination.isSemipositive_smul hγ (by exact_mod_cast hε.le)
  · intro x hx
    rw [mem_iInter₂] at hx
    obtain ⟨W, π, hπ, D, b, hR⟩ := exists_resolutionData hψ
    set β := ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature with hβ
    set Γ := ClosedRealOneOneForm.pullback hπ.1.1 γ with hΓ
    have hbig := isBig_residualClass hR hK
    obtain ⟨C, hC, hCsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul W.omega (-Γ)
    -- `x g ∈ ν(D) + Δ_W(β + ε C ω_W)` for every rational `ε > 0`
    have hstep : ∀ ε : ℚ, 0 < ε → x ᵥ* correctionMatrixReal hπ ∈
        flagValuation W D.weight +ᵥ tradOkounkovBody W (β + ((ε : ℝ) * C) • W.omega.form) := by
      intro ε hε
      have hε' : (0 : ℝ) ≤ ε := by exact_mod_cast hε.le
      have hsemi : (θ + (ε : ℝ) • γ - θ).val.IsSemipositive := by
        rw [add_sub_cancel_left]
        exact KahlerDomination.isSemipositive_smul hγ hε'
      have h1 := image_partialOkounkovBody_subset (isResolutionData_of_le hR hsemi)
        (isKahlerCurrentPotential_of_le hK hsemi) ⟨x, hx ε hε, rfl⟩
      have hform : ClosedRealOneOneForm.pullback hπ.1.1 (θ + (ε : ℝ) • γ) - D.curvature =
          β + (ε : ℝ) • Γ := by
        rw [TranscendentalBody.pullback_add', TranscendentalBody.pullback_smul', hβ, hΓ]
        abel
      rw [hform] at h1
      refine vadd_set_mono (tradOkounkovBody_subset_of_le ?_) h1
      have heq : β + ((ε : ℝ) * C) • W.omega.form - (β + (ε : ℝ) • Γ) =
          (ε : ℝ) • (-Γ + C • W.omega.form) := by
        rw [mul_smul]
        module
      rw [heq]
      exact KahlerDomination.isSemipositive_smul hCsemi hε'
    -- hence `x g - ν(D) ∈ Δ_W(β)`
    have hmem : x ᵥ* correctionMatrixReal hπ - flagValuation W D.weight ∈
        tradOkounkovBody W β := by
      rw [TranscendentalBody.tradOkounkovBody_eq_iInter_add_kahler hbig, mem_iInter₂]
      intro ε' hε'
      have hε'R : (0 : ℝ) < ε' := by exact_mod_cast hε'
      obtain ⟨ε, hε0, hεle⟩ := exists_rat_btwn (div_pos hε'R hC)
      have hε0' : (0 : ℚ) < ε := by exact_mod_cast hε0
      obtain ⟨y, hy, hxy⟩ := hstep ε hε0'
      have hxy' : x ᵥ* correctionMatrixReal hπ - flagValuation W D.weight = y := by
        rw [← hxy]
        show flagValuation W D.weight + y - flagValuation W D.weight = y
        rw [add_sub_cancel_left]
      rw [hxy']
      refine tradOkounkovBody_subset_of_le ?_ hy
      have heq : β + (ε' : ℝ) • W.omega.form - (β + ((ε : ℝ) * C) • W.omega.form) =
          ((ε' : ℝ) - (ε : ℝ) * C) • W.omega.form := by module
      rw [heq]
      refine KahlerDomination.isSemipositive_smul W.omega.isSemipositive ?_
      have h' := (lt_div_iff₀ hC).mp hεle
      linarith
    -- `x g ∈ Δ(θ; ψ) g`
    have hx' : x ᵥ* correctionMatrixReal hπ ∈
        (fun z => z ᵥ* correctionMatrixReal hπ) '' partialOkounkovBody F θ ψ := by
      rw [(TranscendentalL2.partialOkounkovBody_birational hR hK
        (globalAnalyticCurrents_subset_analyticCurrents θ hψ)).2]
      refine ⟨_, hmem, ?_⟩
      show flagValuation W D.weight +
        (x ᵥ* correctionMatrixReal hπ - flagValuation W D.weight) = x ᵥ* correctionMatrixReal hπ
      rw [add_sub_cancel]
    obtain ⟨y, hy, hyx⟩ := hx'
    have hyx' : y = x := by
      have h := congrArg (fun z => z ᵥ* (correctionMatrixReal hπ)⁻¹) hyx
      simpa only [vecMul_correctionMatrixReal_inv] using h
    rwa [← hyx']

end Limit

/-! ### Scaling -/

section Scaling

variable {n : ℕ} {F : OriginalFlagGeometry.{u} n}

/-- `Δ(θ; q ψ) ⊆ q Δ(q⁻¹ θ; ψ)` for `q ∈ ℚ_{>0}`: `S ∈ Ω(θ; q ψ)` gives
`q⁻¹ S ∈ Ω(q⁻¹ θ; ψ)` with `ν(S) = q ν(q⁻¹ S)`. -/
theorem partialOkounkovBody_smul_subset (θ : ClosedRealOneOneForm n F.carrier)
    (ψ : F.carrier → EReal) {q : ℚ} (hq : 0 < q) :
    partialOkounkovBody F θ (fun x => ((q : ℝ) : EReal) * ψ x) ⊆
      (q : ℝ) • partialOkounkovBody F ((q : ℝ)⁻¹ • θ) ψ := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hqi : (0 : ℝ) < (q : ℝ)⁻¹ := inv_pos.mpr hq'
  unfold partialOkounkovBody
  rw [← closure_smul₀]
  refine closure_mono ?_
  rintro _ ⟨s, ⟨⟨hsG, κ, hκ⟩, hsle⟩, rfl⟩
  set s' : F.carrier → EReal := fun x => (((q : ℝ)⁻¹ : ℝ) : EReal) * s x with hs'
  have hs'psh : IsThetaPshPotential ((q : ℝ)⁻¹ • θ).val s' :=
    isThetaPshPotential_nonneg_smul hsG.1 hqi.le
  have hs'G : s' ∈ gentleCurrents ((q : ℝ)⁻¹ • θ) := by
    have h := TranscendentalBody.smul_mem_gentleCurrents (σ := (q : ℝ)⁻¹ • θ) hsG
      (inv_pos.mpr hq) (by simpa only [Rat.cast_inv] using hs'psh)
    simpa only [Rat.cast_inv] using h
  have hs'K : IsKahlerCurrentPotential ((q : ℝ)⁻¹ • θ) s' := by
    refine ⟨KahlerBackground.smul hqi κ, ?_⟩
    have h := isThetaPshPotential_nonneg_smul hκ hqi.le
    rwa [KahlerBackground.smul_form, ← smul_sub]
  have hs'le : SingularityLE s' ψ := by
    refine singularityLE_trans (TranscendentalDensity.singularityLE_smul hsle hqi.le)
      (TranscendentalDensity.singularityLE_of_eq fun x => ?_)
    rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hq'.ne', EReal.coe_one, one_mul]
  have hss' : s = fun x => ((q : ℝ) : EReal) * s' x := by
    funext x
    rw [hs', ← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hq'.ne', EReal.coe_one, one_mul]
  have hν : flagValuation F s = (q : ℝ) • flagValuation F s' := by
    rw [hss']
    exact flagValuation_smul hs'psh hq'.le
  rw [hν]
  exact smul_mem_smul_set ⟨s', ⟨⟨hs'G, hs'K⟩, hs'le⟩, rfl⟩

end Scaling

section ScalingLimit

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- `(1 - a)⁻¹ x ∈ Δ(θ + ε ω; ψ)` if `x ∈ Δ(θ; (1 - a) ψ)`, `a ∈ ℚ ∩ (0, 1/2]` and
`2 a C ≤ ε` with `C ≥ 0` and `C ω - θ ≥ 0`. -/
theorem inv_smul_mem_partialOkounkovBody_add {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {ψ : F.carrier → EReal} {C ε : ℝ} (hC0 : 0 ≤ C)
    (hC : (-θ + C • F.omega.form).val.IsSemipositive)
    {a : ℚ} (ha0 : 0 < a) (ha1 : a ≤ 1 / 2) (haC : 2 * (a : ℝ) * C ≤ ε) {x : Fin (m + 1) → ℝ}
    (hx : x ∈ partialOkounkovBody F θ (fun y => ((1 - (a : ℝ) : ℝ) : EReal) * ψ y)) :
    (1 - (a : ℝ))⁻¹ • x ∈ partialOkounkovBody F (θ + ε • F.omega.form) ψ := by
  have ha0R : (0 : ℝ) < a := by exact_mod_cast ha0
  have ha1R : (a : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr ha1
    push_cast at h
    exact h
  have hq : (0 : ℚ) < 1 - a := by linarith
  have hqR : (((1 - a : ℚ)) : ℝ) = 1 - (a : ℝ) := by push_cast; ring
  have hpos : (0 : ℝ) < 1 - (a : ℝ) := by linarith
  have hx' : x ∈ partialOkounkovBody F θ (fun y => ((((1 - a : ℚ)) : ℝ) : EReal) * ψ y) := by
    rw [hqR]; exact hx
  obtain ⟨y, hy, hyx⟩ := partialOkounkovBody_smul_subset θ ψ hq hx'
  have hy' : y = (1 - (a : ℝ))⁻¹ • x := by
    rw [← hyx, hqR, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
  rw [← hy']
  rw [hqR] at hy
  refine partialOkounkovBody_subset_of_le ?_ ψ hy
  -- `θ + ε ω - (1 - a)⁻¹ θ = s (-θ + C ω) + (ε - s C) ω` with `s = a / (1 - a) ≤ 2 a`
  set s : ℝ := (a : ℝ) / (1 - (a : ℝ)) with hs
  have hs0 : 0 ≤ s := div_nonneg ha0R.le hpos.le
  have hinv : (1 - (a : ℝ))⁻¹ = 1 + s := by
    rw [hs]
    field_simp
    ring
  have hs2 : s ≤ 2 * (a : ℝ) := by
    rw [hs, div_le_iff₀ hpos]
    nlinarith
  have hsC : s * C ≤ ε :=
    calc s * C ≤ 2 * (a : ℝ) * C := by gcongr
      _ ≤ ε := haC
  have heq : θ + ε • F.omega.form - (1 - (a : ℝ))⁻¹ • θ =
      s • (-θ + C • F.omega.form) + (ε - s * C) • F.omega.form := by
    rw [hinv]
    module
  rw [heq]
  exact UniformPerturbedKahlerLowerBound.isSemipositive_add
    (KahlerDomination.isSemipositive_smul hC hs0)
    (KahlerDomination.isSemipositive_smul F.omega.isSemipositive (by linarith))

/-- **`claude-pob:scaling-limit`** (the step `⋂_ε Δ(θ, (1 - ε) φ_j) = Δ(θ, φ_j)` of the book's
proof of `lma:Okounkov:L1517`, here without volumes): for a Kähler current `θ + dd^c ψ`,
`ψ ∈ 𝒜ᵍ(θ)`, if `x ∈ Δ(θ; (1 - a) ψ)` for every rational `a ∈ (0, 1)`, then `x ∈ Δ(θ; ψ)`. -/
theorem mem_partialOkounkovBody_of_forall_smul {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {ψ : F.carrier → EReal} (hψ : ψ ∈ globalAnalyticCurrents θ)
    (hK : IsKahlerCurrentPotential θ ψ) {x : Fin (m + 1) → ℝ}
    (hx : ∀ a : ℚ, 0 < a → a < 1 →
      x ∈ partialOkounkovBody F θ (fun y => ((1 - (a : ℝ) : ℝ) : EReal) * ψ y)) :
    x ∈ partialOkounkovBody F θ ψ := by
  rw [partialOkounkovBody_eq_iInter_add hψ hK F.omega.isSemipositive, mem_iInter₂]
  intro ε hε
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨C, hC, hCsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul F.omega (-θ)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * C / (ε : ℝ))
  -- the rational sequence `a_k = 1 / (k + N + 2)`
  set a : ℕ → ℚ := fun k => 1 / (((k + N + 1 : ℕ) : ℚ) + 1) with ha
  have haR : ∀ k, ((a k : ℚ) : ℝ) = 1 / (((k + N + 1 : ℕ) : ℝ) + 1) := by
    intro k
    rw [ha]
    push_cast
    ring
  have ha0 : ∀ k, 0 < a k := fun k => by rw [ha]; positivity
  have hkN : ∀ k, (N : ℝ) + 2 ≤ ((k + N + 1 : ℕ) : ℝ) + 1 := by
    intro k
    push_cast
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have ha1 : ∀ k, a k ≤ 1 / 2 := by
    intro k
    have h : ((a k : ℚ) : ℝ) ≤ 1 / 2 := by
      rw [haR, div_le_div_iff₀ (by positivity) (by norm_num)]
      have := hkN k
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    have h' : ((a k : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by push_cast; exact h
    exact (Rat.cast_le (K := ℝ)).mp h'
  have haC : ∀ k, 2 * ((a k : ℚ) : ℝ) * C ≤ ε := by
    intro k
    rw [haR]
    have hpos : (0 : ℝ) < ((k + N + 1 : ℕ) : ℝ) + 1 := by positivity
    rw [show 2 * (1 / (((k + N + 1 : ℕ) : ℝ) + 1)) * C = 2 * C / (((k + N + 1 : ℕ) : ℝ) + 1) by
      ring, div_le_iff₀ hpos]
    have h1 : 2 * C / (ε : ℝ) < (N : ℝ) := hN
    rw [div_lt_iff₀ hεR] at h1
    have h2 := hkN k
    nlinarith
  have hmem : ∀ k, (1 - ((a k : ℚ) : ℝ))⁻¹ • x ∈
      partialOkounkovBody F (θ + (ε : ℝ) • F.omega.form) ψ := fun k =>
    inv_smul_mem_partialOkounkovBody_add hC.le hCsemi (ha0 k) (ha1 k) (haC k)
      (hx (a k) (ha0 k) (by linarith [ha1 k]))
  -- `(1 - a_k)⁻¹ x → x`
  have hlim0 : Tendsto (fun k => ((a k : ℚ) : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat (N + 1))
    refine h.congr fun k => ?_
    rw [haR]
    rfl
  have hlim : Tendsto (fun k => (1 - ((a k : ℚ) : ℝ))⁻¹ • x) atTop (𝓝 x) := by
    have h1 : Tendsto (fun k => (1 - ((a k : ℚ) : ℝ))⁻¹) atTop (𝓝 ((1 - 0 : ℝ))⁻¹) :=
      (tendsto_const_nhds.sub hlim0).inv₀ (by norm_num)
    rw [sub_zero, inv_one] at h1
    simpa only [one_smul] using h1.smul_const x
  exact (isClosed_partialOkounkovBody _ ψ).mem_of_tendsto hlim (Eventually.of_forall hmem)

/-- **Comparison form of `claude-pob:scaling-limit`**: if for every rational `a ∈ (0, 1)` some
`V k` is more singular than `(1 - a) ψ` (as `prop:compqequi` provides) and `x ∈ Δ(θ; V k)` for
all `k`, then `x ∈ Δ(θ; ψ)`. -/
theorem mem_partialOkounkovBody_of_forall_singularityLE
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {ψ : F.carrier → EReal}
    (hψ : ψ ∈ globalAnalyticCurrents θ) (hK : IsKahlerCurrentPotential θ ψ)
    {V : ℕ → F.carrier → EReal}
    (hV : ∀ a : ℚ, 0 < a → a < 1 →
      ∃ k, SingularityLE (V k) (fun y => ((1 - (a : ℝ) : ℝ) : EReal) * ψ y))
    {x : Fin (m + 1) → ℝ} (hx : ∀ k, x ∈ partialOkounkovBody F θ (V k)) :
    x ∈ partialOkounkovBody F θ ψ :=
  mem_partialOkounkovBody_of_forall_smul hψ hK fun a ha0 ha1 =>
    let ⟨k, hk⟩ := hV a ha0 ha1
    partialOkounkovBody_mono θ hk (hx k)

end ScalingLimit

end SGPT.Okounkov.PartialBody

import SGPT.Okounkov.PartialBodyGeneral
import SGPT.Okounkov.ModificationQuasiEquisingular

/-!
# Bimeromorphic behaviour of partial Okounkov bodies

Source: the book's `thm:pobmain` (5) (chapter *The theory of Okounkov bodies*, section
*Transcendental partial Okounkov bodies*); blueprint chapter `claude-pob`, node
`claude-pob:birational`.

Let `π : W → X` be a proper bimeromorphic morphism from a compact Kähler manifold carrying the
lifting `(W•, g)` of the flag (`IsFlagLifting F W π`, `g = cor(Y•, π)`). For every
`T = θ + dd^c φ ∈ 𝒵₊(X, α)`, `Δ_{W•}(π^*T) = Δ_{Y•}(T) g` (`generalPartialBody_pullback`).

The book states this for `T` with positive mass and proves it from `thm:pobmain` (4)
(`d_S`-continuity) and `thm:charIgoodasclosure`, reducing to `lma:liftOkounana`. The route here
needs neither (and no positivity of the mass):

* **Kähler currents** (`generalPartialBody_pullback_of_kahler`): for a Kähler approximation
  `(T_k)` of `T`, `(π^*T_k)` is one of `π^*T + ε ω_W` for every `ε > 0`
  (`sourceQuasiEquisingularApproximation_modification_pullback`), so
  `Δ_{W•}(π^*T) = ⋂_k ⋂_{ε > 0} Δ_{W•}(π^*T_k + ε ω_W)`; for fixed `k`, resolution data
  `p^*π^*T_k = [D] + R'` on `V → W` give `Δ_{W•}(π^*T_k + ε ω_W) = (ν([D]) + Δ_V({R'} + ε p^*ω_W)) h⁻¹`
  and the intersection over `ε` is `(ν([D]) + Δ_V({R'})) h⁻¹ = Δ_{Y•}(T_k) g`
  (`TranscendentalPartial.analyticPartialBodyOf_pullback`, i.e. `lma:liftOkounana`), by the Kähler
  limit of `thm:Okounkovtranmain` (4) on `V` (`analyticPartialBodyOf_eq_iInter_add`).
* **General currents**: `Δ_{Y•}(T) g = ⋂_j Δ_{Y•}(T + j⁻¹ ω) g = ⋂_j Δ_{W•}(π^*T + j⁻¹ π^*ω)`,
  and `π^*T ≤ π^*T + j⁻¹ π^*ω ≤ π^*T + j⁻¹ C ω_W` with the monotonicity of the bodies in the
  background form.
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
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.TranscendentalPartial

/-! ### The correction matrix is bijective -/

/-- `x ↦ x g` is bijective (`det g = 1`). -/
theorem bijective_vecMul_correctionMatrixReal {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) :
    Function.Bijective (fun x : Fin n → ℝ => x ᵥ* correctionMatrixReal hπ) := by
  refine ⟨fun x y hxy => ?_, fun y => ⟨y ᵥ* (correctionMatrixReal hπ)⁻¹, ?_⟩⟩
  · have h := congrArg (fun z => z ᵥ* (correctionMatrixReal hπ)⁻¹) hxy
    simpa only [vecMul_correctionMatrixReal_inv] using h
  · show (y ᵥ* (correctionMatrixReal hπ)⁻¹) ᵥ* correctionMatrixReal hπ = y
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_det_correctionMatrixReal hπ),
      Matrix.vecMul_one]

/-! ### Limits of the book's formula in the class -/

section Limit

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- **Limit in a big class for semipositive perturbations**: for `{β}` big and `γ ≥ 0`,
`⋂_{ε ∈ ℚ_{>0}} Δ(β + ε γ) = Δ(β)` (from the Kähler limit, `γ ≤ C ω`). -/
theorem tradOkounkovBody_eq_iInter_add_semipositive {β γ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative β))
    (hγ : γ.val.IsSemipositive) :
    ⋂ (ε : ℚ) (_ : 0 < ε), tradOkounkovBody F (β + (ε : ℝ) • γ) = tradOkounkovBody F β := by
  apply Subset.antisymm
  · obtain ⟨C, hC, hCsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul F.omega (-γ)
    rw [TranscendentalBody.tradOkounkovBody_eq_iInter_add_kahler hbig]
    refine subset_iInter₂ fun ε' hε' => ?_
    have hε'R : (0 : ℝ) < ε' := by exact_mod_cast hε'
    obtain ⟨ε, hε0, hεle⟩ := exists_rat_btwn (div_pos hε'R hC)
    have hε0' : (0 : ℚ) < ε := by exact_mod_cast hε0
    refine (iInter₂_subset ε hε0').trans (tradOkounkovBody_subset_of_le ?_)
    have heq : β + (ε' : ℝ) • F.omega.form - (β + (ε : ℝ) • γ) =
        (ε : ℝ) • (-γ + C • F.omega.form) + ((ε' : ℝ) - (ε : ℝ) * C) • F.omega.form := by
      module
    rw [heq]
    have h' := (lt_div_iff₀ hC).mp hεle
    exact UniformPerturbedKahlerLowerBound.isSemipositive_add
      (KahlerDomination.isSemipositive_smul hCsemi hε0.le)
      (KahlerDomination.isSemipositive_smul F.omega.isSemipositive (by linarith))
  · refine subset_iInter₂ fun ε hε => tradOkounkovBody_subset_of_le ?_
    rw [add_sub_cancel_left]
    exact KahlerDomination.isSemipositive_smul hγ (by exact_mod_cast hε.le)

/-- The book's formula `Δ_W({π^*θ - Θ_D}) g⁻¹ + ν_W([D]) g⁻¹` increases with the background. -/
theorem analyticPartialBodyOf_subset_of_le {θ θ' : ClosedRealOneOneForm (m + 1) F.carrier}
    {W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π)
    (D : MeteredEffectiveQDivisor (m + 1) W.carrier) (hle : (θ' - θ).val.IsSemipositive) :
    analyticPartialBodyOf θ hπ D ⊆ analyticPartialBodyOf θ' hπ D := by
  rw [analyticPartialBodyOf_eq_image, analyticPartialBodyOf_eq_image]
  refine image_mono (vadd_set_mono (tradOkounkovBody_subset_of_le ?_))
  have heq : ClosedRealOneOneForm.pullback hπ.1.1 θ' - D.curvature -
      (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature) =
        ClosedRealOneOneForm.pullback hπ.1.1 (θ' - θ) := by
    rw [TranscendentalBody.pullback_sub']
    abel
  rw [heq]
  exact ClosedRealOneOneForm.pullback_isSemipositive hπ.1.1 hle

/-- **Limit of the book's formula in the class** (blueprint `claude-pob:formula-limit`): for a
lifting `(W•, g)`, a metered divisor `D` on `W` with `{π^*θ - Θ_D}` big and `γ ≥ 0`,
`⋂_{ε ∈ ℚ_{>0}} (Δ_W({π^*(θ + εγ) - Θ_D}) + ν_W([D])) g⁻¹ = (Δ_W({π^*θ - Θ_D}) + ν_W([D])) g⁻¹`. -/
theorem analyticPartialBodyOf_eq_iInter_add {θ γ : ClosedRealOneOneForm (m + 1) F.carrier}
    {W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π)
    (D : MeteredEffectiveQDivisor (m + 1) W.carrier)
    (hbig : SGPT.PSH.BookCurrent.IsBig
      (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature)))
    (hγ : γ.val.IsSemipositive) :
    ⋂ (ε : ℚ) (_ : 0 < ε), analyticPartialBodyOf (θ + (ε : ℝ) • γ) hπ D =
      analyticPartialBodyOf θ hπ D := by
  apply Subset.antisymm
  · intro x hx
    rw [mem_iInter₂] at hx
    set β := ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature with hβ
    set Γ := ClosedRealOneOneForm.pullback hπ.1.1 γ with hΓ
    have hΓsemi : Γ.val.IsSemipositive := ClosedRealOneOneForm.pullback_isSemipositive hπ.1.1 hγ
    have hstep : ∀ ε : ℚ, 0 < ε → x ᵥ* correctionMatrixReal hπ - flagValuation W D.weight ∈
        tradOkounkovBody W (β + (ε : ℝ) • Γ) := by
      intro ε hε
      have h := hx ε hε
      rw [analyticPartialBodyOf_eq_image] at h
      obtain ⟨y, ⟨z, hz, rfl⟩, hyx⟩ := h
      have hform : ClosedRealOneOneForm.pullback hπ.1.1 (θ + (ε : ℝ) • γ) - D.curvature =
          β + (ε : ℝ) • Γ := by
        rw [TranscendentalBody.pullback_add', TranscendentalBody.pullback_smul', hβ, hΓ]
        abel
      rw [hform] at hz
      have hxg : x ᵥ* correctionMatrixReal hπ = flagValuation W D.weight + z := by
        rw [← hyx]
        show ((flagValuation W D.weight + z) ᵥ* (correctionMatrixReal hπ)⁻¹) ᵥ*
          correctionMatrixReal hπ = _
        rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_det_correctionMatrixReal hπ),
          Matrix.vecMul_one]
      rw [hxg, add_sub_cancel_left]
      exact hz
    have hmem : x ᵥ* correctionMatrixReal hπ - flagValuation W D.weight ∈ tradOkounkovBody W β := by
      rw [← tradOkounkovBody_eq_iInter_add_semipositive hbig hΓsemi, mem_iInter₂]
      exact hstep
    rw [analyticPartialBodyOf_eq_image]
    refine ⟨x ᵥ* correctionMatrixReal hπ, ⟨_, hmem, ?_⟩, vecMul_correctionMatrixReal_inv hπ x⟩
    show flagValuation W D.weight +
      (x ᵥ* correctionMatrixReal hπ - flagValuation W D.weight) = x ᵥ* correctionMatrixReal hπ
    rw [add_sub_cancel]
  · refine subset_iInter₂ fun ε hε => analyticPartialBodyOf_subset_of_le hπ D ?_
    rw [add_sub_cancel_left]
    exact KahlerDomination.isSemipositive_smul hγ (by exact_mod_cast hε.le)

end Limit

/-! ### Pullbacks -/

section Pullback

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- Monotonicity of the general bodies in the background form. -/
theorem generalPartialBody_subset_of_le {θ θ' : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hle : (θ' - θ).val.IsSemipositive) :
    generalPartialBody F θ φ ⊆ generalPartialBody F θ' φ := by
  refine iInter_mono fun j => kahlerPartialBody_subset_of_le
    (isKahlerCurrentPotential_add_smul hφ F.omega (t := ((j : ℝ) + 1)⁻¹) (by positivity)) ?_
  have heq : θ' + ((j : ℝ) + 1)⁻¹ • F.omega.form - (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form) =
      θ' - θ := by abel
  rwa [heq]

/-- For a Kähler current `T_k ∈ 𝒜ᵍ(ξ)` and a lifting `(W•, g)`:
`⋂_{ε > 0} Δ_{W•}(π^*T_k + ε ω_W) = Δ_{Y•}(T_k) g` (DRWNXZ bodies). -/
theorem iInter_partialOkounkovBody_pullback_add {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {ψ : F.carrier → EReal} (hψ : ψ ∈ globalAnalyticCurrents θ)
    (hK : IsKahlerCurrentPotential θ ψ) {W : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) :
    ⋂ (ε : ℝ) (_ : 0 < ε), partialOkounkovBody W
        (ClosedRealOneOneForm.pullback hπ.1.1 θ + ε • W.omega.form) (fun y => ψ (π y)) =
      (fun x => x ᵥ* correctionMatrixReal hπ) '' partialOkounkovBody F θ ψ := by
  set θW := ClosedRealOneOneForm.pullback hπ.1.1 θ with hθW
  have hψW : (fun y => ψ (π y)) ∈ globalAnalyticCurrents θW := comp_mem_globalAnalyticCurrents hπ.1 hψ
  obtain ⟨V, p, hp, D, b, hR⟩ := exists_resolutionData hψW
  have hA : ψ ∈ analyticCurrents θ := globalAnalyticCurrents_subset_analyticCurrents θ hψ
  -- the bigness of the residual class on `V`, through the composite lifting `π ∘ p`
  obtain ⟨hπp, -⟩ := flagLifting_comp_correction hπ hp
  have hgeom : (ClosedRealOneOneForm.pullback hπp.1.1 θ - D.curvature).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback hp.1.1 θW - D.curvature).val :=
    geometricallyEq_sub (SmoothRealForm.pullback_comp_geometricallyEq hπ.1.1 hp.1.1 θ.val) _
  have hR' : IsResolutionData θ ψ hπp D b :=
    ⟨(hgeom.thetaPshPotential_iff b).mpr hR.psh, hR.bounded, fun y => hR.eq y⟩
  have hbig : SGPT.PSH.BookCurrent.IsBig
      (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hp.1.1 θW - D.curvature)) := by
    rw [← RealBottChern.ofRepresentative_eq_of_geometricallyEq hgeom]
    exact isBig_residualClass hR' hK
  -- each perturbed body is the book's formula for the same data
  have hle : ∀ ε : ℝ, 0 ≤ ε → (θW + ε • W.omega.form - θW).val.IsSemipositive := fun ε hε => by
    rw [add_sub_cancel_left]
    exact KahlerDomination.isSemipositive_smul W.omega.isSemipositive hε
  have hψWpsh : IsThetaPshPotential θW.val (fun y => ψ (π y)) := hψW.1
  have hbody : ∀ ε : ℝ, 0 < ε → partialOkounkovBody W (θW + ε • W.omega.form) (fun y => ψ (π y)) =
      analyticPartialBodyOf (θW + ε • W.omega.form) hp D := fun ε hε =>
    (analyticPartialBodyOf_eq_partialOkounkovBody TranscendentalL2.pushforwardAnalyticStatement
      (isResolutionData_of_le hR (hle ε hε.le))
      (isKahlerCurrentPotential_add_smul hψWpsh W.omega hε)
      ⟨TranscendentalBody.isThetaPshPotential_of_le hψW.1 (hle ε hε.le),
        (globalAnalyticCurrents_subset_analyticCurrents θW hψW).2⟩).symm
  rw [← analyticPartialBodyOf_pullback TranscendentalL2.pushforwardAnalyticStatement hK hA hπ hR,
    ← analyticPartialBodyOf_eq_iInter_add hp D hbig W.omega.isSemipositive]
  apply Subset.antisymm
  · refine subset_iInter₂ fun ε hε => ?_
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    rw [← hbody ε hε']
    exact iInter₂_subset (ε : ℝ) hε'
  · refine subset_iInter₂ fun ε hε => ?_
    rw [hbody ε hε]
    obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
    have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
    refine (iInter₂_subset q hq0').trans (analyticPartialBodyOf_subset_of_le hp D ?_)
    have heq : θW + ε • W.omega.form - (θW + (q : ℝ) • W.omega.form) =
        (ε - (q : ℝ)) • W.omega.form := by module
    rw [heq]
    exact KahlerDomination.isSemipositive_smul W.omega.isSemipositive (by linarith)

/-- **`thm:pobmain` (5) for Kähler currents**: for a Kähler current `T = θ + dd^c φ` and a
lifting `(W•, g)` along `π : W → X`, `Δ_{W•}(π^*T) = Δ_{Y•}(T) g` (`π^*T` is in general not a
Kähler current; its body is the one of `def:generalPOB`). -/
theorem generalPartialBody_pullback_of_kahler {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsKahlerCurrentPotential θ φ)
    {W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) :
    generalPartialBody W (ClosedRealOneOneForm.pullback hπ.1.1 θ) (fun y => φ (π y)) =
      (fun x => x ᵥ* correctionMatrixReal hπ) '' kahlerPartialBody F θ φ := by
  set θW := ClosedRealOneOneForm.pullback hπ.1.1 θ with hθW
  have hφθ := isThetaPshPotential_of_isKahlerCurrentPotential hφ
  have hφW : IsThetaPshPotential θW.val (fun y => φ (π y)) :=
    AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification hπ.1 θ hφθ
  obtain ⟨U, hU⟩ := exists_isKahlerQEA hφ
  -- the pulled back approximation
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  let _ : MeasurableSpace W.carrier := borel W.carrier
  have _ : BorelSpace W.carrier := ⟨rfl⟩
  have hUW : SourceQuasiEquisingularApproximation θW (fun y => φ (π y))
      (fun k y => U k (π y)) :=
    sourceQuasiEquisingularApproximation_modification_pullback hπ.1 W.omega θ hU.1
  have hle : ∀ ε : ℝ, 0 ≤ ε → (θW + ε • W.omega.form - θW).val.IsSemipositive := fun ε hε => by
    rw [add_sub_cancel_left]
    exact KahlerDomination.isSemipositive_smul W.omega.isSemipositive hε
  have hQ : ∀ ε : ℝ, 0 < ε → IsKahlerQEA (θW + ε • W.omega.form) (fun y => φ (π y))
      (fun k y => U k (π y)) := fun ε hε =>
    ⟨sourceQuasiEquisingularApproximation_of_le hUW (hle ε hε.le), fun k =>
      ⟨⟨TranscendentalBody.isThetaPshPotential_of_le
          (comp_mem_globalAnalyticCurrents hπ.1 (hU.2 k).1).1 (hle ε hε.le),
        (comp_mem_globalAnalyticCurrents hπ.1 (hU.2 k).1).2⟩,
       isKahlerCurrentPotential_add_smul
        (comp_mem_globalAnalyticCurrents hπ.1 (hU.2 k).1).1 W.omega hε⟩⟩
  rw [generalPartialBody_eq_iInter_pos hφW, kahlerPartialBody_eq_iInter hU,
    image_iInter (bijective_vecMul_correctionMatrixReal hπ)]
  simp_rw [← iInter_partialOkounkovBody_pullback_add (hU.2 _).1 (hU.2 _).2 hπ]
  ext x
  simp only [mem_iInter]
  constructor
  · intro h k ε hε
    have h' := h ε hε
    rw [kahlerPartialBody_eq_iInter (hQ ε hε), mem_iInter] at h'
    exact h' k
  · intro h ε hε
    rw [kahlerPartialBody_eq_iInter (hQ ε hε), mem_iInter]
    exact fun k => h k ε hε

/-- **`thm:pobmain` (5)** (bimeromorphic invariance): for a proper bimeromorphic morphism
`π : W → X` from a compact Kähler manifold carrying the lifting `(W•, g)` of the flag and every
`T = θ + dd^c φ ∈ 𝒵₊(X, α)`, `Δ_{W•}(π^*T) = Δ_{Y•}(T) g`. The book assumes `T ∈ 𝒵₊(X, α)_{>0}`;
the statement holds for every `T`. Unconditional. -/
theorem generalPartialBody_pullback {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) :
    generalPartialBody W (ClosedRealOneOneForm.pullback hπ.1.1 θ) (fun y => φ (π y)) =
      (fun x => x ᵥ* correctionMatrixReal hπ) '' generalPartialBody F θ φ := by
  set θW := ClosedRealOneOneForm.pullback hπ.1.1 θ with hθW
  set ωX := ClosedRealOneOneForm.pullback hπ.1.1 F.omega.form with hωX
  have hωXsemi : ωX.val.IsSemipositive :=
    ClosedRealOneOneForm.pullback_isSemipositive hπ.1.1 F.omega.isSemipositive
  have hφW : IsThetaPshPotential θW.val (fun y => φ (π y)) :=
    AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification hπ.1 θ hφ
  have ht0 : ∀ j : ℕ, (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := fun j => by positivity
  -- the Kähler case for `T + j⁻¹ ω`
  have hpull : ∀ j : ℕ, (fun x => x ᵥ* correctionMatrixReal hπ) ''
      kahlerPartialBody F (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form) φ =
        generalPartialBody W (θW + ((j : ℝ) + 1)⁻¹ • ωX) (fun y => φ (π y)) := by
    intro j
    rw [← generalPartialBody_pullback_of_kahler (isKahlerCurrentPotential_add_smul hφ F.omega (ht0 j))
      hπ, TranscendentalBody.pullback_add', TranscendentalBody.pullback_smul']
  conv_rhs => rw [generalPartialBody, image_iInter (bijective_vecMul_correctionMatrixReal hπ)]
  rw [iInter_congr hpull]
  apply Subset.antisymm
  · refine subset_iInter fun j => generalPartialBody_subset_of_le hφW ?_
    rw [add_sub_cancel_left]
    exact KahlerDomination.isSemipositive_smul hωXsemi (ht0 j).le
  · obtain ⟨C, hC, hCsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul W.omega (-ωX)
    intro x hx
    rw [mem_iInter] at hx
    rw [generalPartialBody, mem_iInter]
    intro i
    -- choose `j` with `(C + 1) j⁻¹ ≤ i⁻¹`
    obtain ⟨j, hj⟩ := exists_nat_gt ((C + 1) * ((i : ℝ) + 1))
    have hxj := hx j
    rw [generalPartialBody, mem_iInter] at hxj
    have hxj' := hxj j
    have hφj : IsThetaPshPotential (θW + ((j : ℝ) + 1)⁻¹ • ωX).val (fun y => φ (π y)) := by
      refine TranscendentalBody.isThetaPshPotential_of_le hφW ?_
      rw [add_sub_cancel_left]
      exact KahlerDomination.isSemipositive_smul hωXsemi (ht0 j).le
    refine kahlerPartialBody_subset_of_le (isKahlerCurrentPotential_add_smul hφj W.omega (ht0 j))
      ?_ hxj'
    have hcoef : ((j : ℝ) + 1)⁻¹ * (C + 1) ≤ ((i : ℝ) + 1)⁻¹ := by
      rw [inv_mul_le_iff₀ (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith
    have heq : θW + ((i : ℝ) + 1)⁻¹ • W.omega.form -
        (θW + ((j : ℝ) + 1)⁻¹ • ωX + ((j : ℝ) + 1)⁻¹ • W.omega.form) =
        ((j : ℝ) + 1)⁻¹ • (-ωX + C • W.omega.form) +
          (((i : ℝ) + 1)⁻¹ - ((j : ℝ) + 1)⁻¹ * (C + 1)) • W.omega.form := by module
    rw [heq]
    exact UniformPerturbedKahlerLowerBound.isSemipositive_add
      (KahlerDomination.isSemipositive_smul hCsemi (ht0 j).le)
      (KahlerDomination.isSemipositive_smul W.omega.isSemipositive (by linarith))

end Pullback

end SGPT.Okounkov.PartialBody

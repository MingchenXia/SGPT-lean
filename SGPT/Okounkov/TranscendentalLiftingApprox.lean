import SGPT.Okounkov.TranscendentalLiftingResolution
import SGPT.Okounkov.TranscendentalRelGenStatement
import SGPT.Okounkov.MultiplierCancellation

/-!
# Approximation of currents on a modification by pushforwards with analytic singularities

Source: blueprint node `tok:approx-pushforward` (chapter `claude-okounkov-transcendental`), i.e.
DRWNXZ (Darvas--Reboulet--Witt Nyström--Xia--Zhang, *Transcendental Okounkov bodies*)
Proposition 4.4.

Let `(W•, g)` be the lifting of the flag `Y•` of `X` along `π : W → X`
(`IsFlagLifting F W π`, `g = correctionMatrixReal hπ`), `θ` a closed real `(1,1)`-form on `X`
and `T = π^*θ + dd^c ψ ∈ 𝒜ᵍ(W, π^*ξ)` a Kähler current (for instance `T ∈ Ω(W, π^*ξ)`). Then
(`exists_analytic_approximation_of_lifting`) there are `w ∈ ℝⁿ` with `w₀ = 0` and Kähler currents
`θ + dd^c φ_k ∈ 𝒜(X, ξ)`, `φ_k ⪯ π_* ψ`, with `ν_{Y•}(φ_k) g = ν_{W•}(ψ) + (k + 1)⁻¹ w` for every
`k`; in particular `ν_{Y•}(φ_k) g → ν_{W•}(T)` and `ν_{Y•}(φ_k)₀ = ν_{W•}(T)₀`
(`flagValuation_zero_of_approximation`).

**This theorem is conditional** on `TranscendentalRelGen.PushforwardAnalyticStatement` (DRWNXZ
Lemma 2.8, `tok:boucksom-pushforward`), an explicit hypothesis `hP`. RELGEN proves it from
`TranscendentalRelGen.WeaklyPseudoconvexL2GenerationStatement` (Nadel/Hörmander `L²` generation on
weakly pseudoconvex Kähler manifolds), which is not yet available.

## The proof (DRWNXZ Proposition 4.4, route of the blueprint)

1. `tok:resolution-lifting` (`exists_logResolution_flagLifting`): a blow-up sequence `p : V → W`
   with a lifted flag `V•` (correction `h`) and a metered effective `ℚ`-divisor `D` on `V` with
   `ψ ∘ p = ψ_D + b`, `b` bounded.
2. `tok:ext-blowup-kahler` (`exists_exceptional_kahler_perturbation`, applied to the Kähler
   form `κ ≤ T`): an exceptional `ℚ`-divisor `E` with `p^*T - ε Θ_E` a Kähler current for small
   `ε`; we use `ε_k = q₀ / (k + 1)`, `q₀ ∈ ℚ_{>0}`.
3. Book `lma:logsingrem` (`exists_kahlerForm_of_logSingularities`): since
   `(p^*π^*θ - ε_k Θ_E) + dd^c(ψ ∘ p)` is a Kähler current with log singularities along `D`, the
   form `β_k = p^*π^*θ - ε_k Θ_E - Θ_D + dd^c h_k` is Kähler; so with `D_k = D + ε_k E`,
   `{(π ∘ p)^*θ} = {β_k} + {D_k}`.
4. `D_k` is `q⁻¹` times an integral divisor with a smooth metric (`exists_integralModel`), and the
   potential `u_k = ψ ∘ p + ε_k ψ_E = ψ_{D_k} + b` (its current is `β_k + [D_k] + dd^c(b - h_k)`,
   a Kähler current) descends to `φ_k ∈ PSH(X, θ)`
   (`tok:zariski-bijection`, `exists_descent`); `PushforwardAnalyticStatement` gives
   `φ_k ∈ 𝒜(X, ξ)`.
5. Valuations (`okflag:actual-whole-current-correction-matrix`, `tok:valuation-divisor`):
   `ν_{Y•}(φ_k) g h = ν_{V•}(u_k) = ν_{V•}(ψ ∘ p) + ε_k ν_{V•}(ψ_E)
   = ν_{W•}(ψ) h + ε_k ν_{V•}(ψ_E)`,
   and `det h = 1`, so `ν_{Y•}(φ_k) g = ν_{W•}(ψ) + ε_k ν_{V•}(ψ_E) h⁻¹`.

The first coordinate: `ν_{V•}(ψ_E)₀ = 0` since `E` is supported in the exceptional locus of `p`
and the lifted `V₁` is not (`IsFlagLifting.exists_mem_first_notMem_exceptionalLocus`), and
correction matrices preserve the first coordinate.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalLifting

open Set Filter
open scoped Topology Manifold ContDiff Matrix
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalRelGen

section Aux

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem geometricallyEq_sub {a b : ClosedRealOneOneForm n M} (h : a.val.GeometricallyEq b.val)
    (c : ClosedRealOneOneForm n M) : (a - c).val.GeometricallyEq (b - c).val := by
  intro e z hz
  rw [BlowupBigPullback.coeff_sub, BlowupBigPullback.coeff_sub, h e hz]

/-- `θ` and `θ + dd^c h` have the same class. -/
theorem ofRepresentative_add_ddc (θ : ClosedRealOneOneForm n M) {h : M → ℝ}
    (hh : ChartSmooth (n := n) h) :
    RealBottChern.ofRepresentative (θ + ManifoldTubePositivity.ddcClosedForm h hh) =
      RealBottChern.ofRepresentative θ := by
  refine ((RealBottChern.ofRepresentative_eq_iff _ _).mpr ?_).symm
  refine ⟨h, hh, fun e z hz => ?_⟩
  rw [ClosedRealOneOneForm.coeff_add, ManifoldTubePositivity.ddcClosedForm_coeff]

/-- `(1/q) (q x) = x` in `EReal` for `q > 0`. -/
theorem ereal_inv_mul_mul {q : ℝ} (hq : 0 < q) (x : EReal) :
    ((1 / q : ℝ) : EReal) * ((q : EReal) * x) = x := by
  rw [← mul_assoc, ← EReal.coe_mul, one_div_mul_cancel hq.ne', EReal.coe_one, one_mul]

end Aux

/-- **Approximation of currents on a modification** (blueprint `tok:approx-pushforward`, DRWNXZ
Proposition 4.4), conditional on `PushforwardAnalyticStatement` (DRWNXZ Lemma 2.8). Let `(W•, g)`
be a lifting of `Y•` along `π` and `T = π^*θ + dd^c ψ ∈ 𝒜ᵍ(W, π^*ξ)` a Kähler current with
analytic singularities of a global type. There are a vector `w` with `w₀ = 0` and Kähler currents
`T_k = θ + dd^c φ_k ∈ 𝒜(X, ξ)` with `T_k ⪯ π_* T` (i.e. `φ_k ⪯ χ` for the potential `χ` of `π_* T`,
`χ ∘ π = ψ`) and `ν_{Y•}(T_k) g = ν_{W•}(T) + (k + 1)⁻¹ w`; equivalently
`ν_{Y•}(T_k) = ν_{W•}(T) g⁻¹ + (k + 1)⁻¹ w g⁻¹`, where `(w g⁻¹)₀ = w₀ = 0`. -/
theorem exists_analytic_approximation_of_lifting (hP : PushforwardAnalyticStatement.{u})
    {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {ψ : W.carrier → EReal}
    (hψ : ψ ∈ globalAnalyticCurrents (ClosedRealOneOneForm.pullback hπ.1.1 θ))
    (hK : IsKahlerCurrentPotential (ClosedRealOneOneForm.pullback hπ.1.1 θ) ψ) :
    ∃ (w : Fin (m + 1) → ℝ) (φ : ℕ → F.carrier → EReal), w 0 = 0 ∧
      (∀ k, φ k ∈ analyticCurrents θ) ∧ (∀ k, IsKahlerCurrentPotential θ (φ k)) ∧
      (∀ k, ∀ χ : F.carrier → EReal, (∀ x, χ (π x) = ψ x) → SGPT.PSH.SingularityLE (φ k) χ) ∧
      (∀ k, flagValuation F (φ k) ᵥ* correctionMatrixReal hπ =
        flagValuation W ψ + ((1 : ℝ) / ((k : ℝ) + 1)) • w) := by
  classical
  set θ' := ClosedRealOneOneForm.pullback hπ.1.1 θ with hθ'
  obtain ⟨hψpot, c, 𝔞, htype⟩ := hψ
  -- Step 1: log resolution with a lifted flag
  obtain ⟨V, p, hp, D, hV, ⟨L⟩, -, -⟩ := exists_logResolution_flagLifting W θ' hψpot htype
  -- Step 2: the exceptional perturbation along `p`
  obtain ⟨κ, hκ⟩ := hK
  obtain ⟨E, hEsupp, -, hpert⟩ := exists_exceptional_kahler_perturbation κ hp
  obtain ⟨ε₀, hε₀, hpert⟩ := hpert θ' ψ ⟨κ, hκ⟩
  obtain ⟨q₀, hq₀, hq₀ε⟩ := exists_rat_btwn hε₀
  have hq₀pos : (0 : ℚ) < q₀ := by exact_mod_cast hq₀
  -- the composite lifting
  have hρ : IsFlagLifting F V (π ∘ p) := hπ.comp hV
  set A := correctionMatrixReal hπ with hA
  set B := correctionMatrixReal hV with hB
  have hAB : correctionMatrixReal hρ = A * B := correctionMatrixReal_comp hπ hV hρ
  set z := flagValuation V E.weight with hz
  have hEpot : IsThetaPshPotential E.curvature.val E.weight := isThetaPshPotential_weight E
  -- the first coordinate of `z` vanishes: `E` is exceptional and `V₁` is not
  have hz0 : z 0 = 0 := by
    obtain ⟨v, hv, hvE⟩ := IsFlagLifting.exists_mem_first_notMem_exceptionalLocus hV
    exact flagValuation_zero_eq_zero_of_ne_bot V hEpot hv (fun h => hvE (hEsupp h))
  refine ⟨(q₀ : ℝ) • (z ᵥ* B⁻¹), ?_⟩
  -- the potential of `π^*T` upstairs
  have hψp : IsThetaPshPotential (ClosedRealOneOneForm.pullback hp.contMDiff θ').val
      (fun y => ψ (p y)) :=
    AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
      hV.1 θ' hψpot
  have hνψp : flagValuation V (fun y => ψ (p y)) = flagValuation W ψ ᵥ* B :=
    flagValuation_comp_eq_vecMul hV hψpot
  obtain ⟨K, hK⟩ := MeteredDivisorScaling.exists_forall_weight_le E
  have key : ∀ k : ℕ, ∃ φ : F.carrier → EReal, φ ∈ analyticCurrents θ ∧
      IsKahlerCurrentPotential θ φ ∧
      (∀ χ : F.carrier → EReal, (∀ x, χ (π x) = ψ x) → SGPT.PSH.SingularityLE φ χ) ∧
      flagValuation F φ ᵥ* A =
        flagValuation W ψ + ((1 : ℝ) / ((k : ℝ) + 1)) • ((q₀ : ℝ) • (z ᵥ* B⁻¹)) := by
    intro k
    set ε : ℚ := q₀ / ((k : ℚ) + 1) with hεdef
    have hk1 : (0 : ℚ) < (k : ℚ) + 1 := by positivity
    have hε : 0 < ε := div_pos hq₀pos hk1
    have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    have hεle : (ε : ℝ) ≤ ε₀ := by
      have h1 : (ε : ℝ) ≤ (q₀ : ℝ) := by
        have : ε ≤ q₀ := div_le_self hq₀pos.le (by linarith)
        exact_mod_cast this
      linarith
    -- Step 2: `p^*T - ε Θ_E` is a Kähler current
    have hKk := hpert (ε : ℝ) hεR hεle
    set σ := ClosedRealOneOneForm.pullback hp.contMDiff θ' - (ε : ℝ) • E.curvature with hσ
    -- Step 3: the Kähler form `β = σ - Θ_D + dd^c h`
    obtain ⟨h, hh, hβ⟩ := exists_kahlerForm_of_logSingularities hKk L
    set β := (σ - D.curvature) + ManifoldTubePositivity.ddcClosedForm h hh with hβdef
    -- Step 4: the divisor `D_k = D + ε E` and its integral model
    set Dk := MeteredDivisorOperations.add D (MeteredDivisorScaling.smul hε.le E) with hDk
    obtain ⟨q, hq, Dint, hDint⟩ := exists_integralModel Dk
    set E' := MeteredDivisorScaling.smul (c := (q : ℚ)) (Nat.cast_nonneg q) Dk with hE'
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    -- the potential `u = ψ ∘ p + ε ψ_E`
    set u : V.carrier → EReal := fun y => ψ (p y) + ((ε : ℝ) : EReal) * E.weight y with hu
    obtain ⟨κk, hκk⟩ := hKk
    have hψσ : IsThetaPshPotential σ.val (fun y => ψ (p y)) := by
      have h0 := LocalPotentials.isThetaPshPotential_add_of_semipositive hκk κk.isSemipositive
      rwa [sub_add_cancel] at h0
    have hεE : IsThetaPshPotential ((ε : ℝ) • E.curvature).val
        (fun y => ((ε : ℝ) : EReal) * E.weight y) :=
      isThetaPshPotential_weight (MeteredDivisorScaling.smul hε.le E)
    have hupot : IsThetaPshPotential (ClosedRealOneOneForm.pullback hp.contMDiff θ').val u := by
      have h0 := isThetaPshPotential_add_from_positive_sum hψσ hεE
      rwa [hσ, sub_add_cancel] at h0
    have hukah : IsKahlerCurrentPotential (ClosedRealOneOneForm.pullback hp.contMDiff θ') u := by
      refine ⟨κk, ?_⟩
      have h0 := isThetaPshPotential_add_from_positive_sum hκk hεE
      have heq : σ - κk.form + (ε : ℝ) • E.curvature =
          ClosedRealOneOneForm.pullback hp.contMDiff θ' - κk.form := by
        rw [hσ]
        abel
      rwa [heq] at h0
    -- transport to `(π ∘ p)^*θ`
    have hgeom : (ClosedRealOneOneForm.pullback hρ.1.1 θ).val.GeometricallyEq
        (ClosedRealOneOneForm.pullback hp.contMDiff θ').val :=
      SmoothRealForm.pullback_comp_geometricallyEq hπ.1.1 hp.contMDiff θ.val
    have hupot' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hρ.1.1 θ).val u :=
      (hgeom.thetaPshPotential_iff u).mpr hupot
    -- descent to `X`
    obtain ⟨φ, hφ, hφu⟩ := exists_descent hρ.1 θ hupot'
    have hφu' : (fun y => φ ((π ∘ p) y)) = u := funext hφu
    refine ⟨φ, ?_, ?_, ?_, ?_⟩
    · -- `φ ∈ 𝒜(X, ξ)` by the pushforward theorem
      have hclass : RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hρ.1.1 θ) =
          RealBottChern.ofRepresentative β +
            (((1 / (q : ℚ) : ℚ) : ℝ)) • RealBottChern.ofRepresentative E'.curvature := by
        rw [RealBottChern.ofRepresentative_eq_of_geometricallyEq hgeom, hE',
          MeteredDivisorScaling.curvature_smul, RealBottChern.ofRepresentative_smul, smul_smul]
        have hqq : ((1 / (q : ℚ) : ℚ) : ℝ) * (((q : ℚ) : ℝ)) = 1 := by
          push_cast
          field_simp
        rw [hqq, one_smul, ← RealBottChern.ofRepresentative_add, hβdef]
        have hform : σ - D.curvature + ManifoldTubePositivity.ddcClosedForm h hh + Dk.curvature =
            ClosedRealOneOneForm.pullback hp.contMDiff θ' +
              ManifoldTubePositivity.ddcClosedForm h hh := by
          rw [hDk, hσ]
          change _ + (D.curvature + (((ε : ℚ) : ℝ)) • E.curvature) = _
          abel
        rw [hform, ofRepresentative_add_ddc]
      have hq1 : (0 : ℚ) < 1 / (q : ℚ) := by
        have : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
        positivity
      refine hP (m + 1) F.carrier V.carrier (π ∘ p) hρ.1 θ β Dint E' (1 / (q : ℚ)) hq1 hβ
        hDint hclass φ hφ ⟨L.residual, L.bound, L.residual_bound, fun y => ?_⟩
      rw [hφu y, hE', MeteredDivisorScaling.weight_smul, Rat.cast_natCast,
        show (((1 / (q : ℚ) : ℚ) : ℝ)) = 1 / (q : ℝ) by push_cast; ring,
        ereal_inv_mul_mul hqR, hDk, MeteredDivisorScaling.weight_add,
        MeteredDivisorScaling.weight_smul, hu]
      simp only
      rw [L.weight_add y]
      exact add_right_comm _ _ _
    · -- the pushforward is a Kähler current
      apply pushforward_isKahlerCurrentPotential hρ.1 F.omega
      obtain ⟨κk', hκk'⟩ := hukah
      refine ⟨κk', ?_⟩
      rw [hφu']
      exact ((geometricallyEq_sub hgeom κk'.form).thetaPshPotential_iff u).mpr hκk'
    · -- `φ ⪯ π_* ψ`: `u = ψ ∘ p + ε ψ_E ≤ ψ ∘ p + ε K`
      intro χ hχ
      refine (singularityLE_comp_iff hρ.1).mp ((SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
        ⟨(ε : ℝ) * K, fun y => ?_⟩)
      have hy : φ ((π ∘ p) y) = u y := hφu y
      simp only [Function.comp_apply] at hy ⊢
      rw [hy, hu, hχ (p y), EReal.coe_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hK y) (EReal.coe_nonneg.mpr hεR.le))
    · -- the valuation
      have hν1 : flagValuation V u = flagValuation F φ ᵥ* (A * B) := by
        rw [← hφu', ← hAB]
        exact flagValuation_comp_eq_vecMul hρ hφ
      have hν2 : flagValuation V u = flagValuation V (fun y => ψ (p y)) + (ε : ℝ) • z := by
        have h0 := flagValuation_add_smul (F := V) hψp hEpot (a := 1) (b := (ε : ℝ)) zero_le_one
          hεR.le
        simp only [EReal.coe_one, one_mul, one_smul] at h0
        exact h0
      rw [hν2, hνψp, ← Matrix.vecMul_vecMul] at hν1
      have h2 := congrArg (fun x => x ᵥ* B⁻¹) hν1
      rw [vecMul_correctionMatrixReal_inv hV, Matrix.add_vecMul,
        vecMul_correctionMatrixReal_inv hV, Matrix.smul_vecMul] at h2
      rw [← h2, smul_smul]
      congr 2
      rw [hεdef]
      push_cast
      ring
  choose φ hφA hφK hφS hφν using key
  refine ⟨φ, ?_, hφA, hφK, hφS, hφν⟩
  rw [Pi.smul_apply, vecMul_correctionMatrixReal_inv_zero hV, hz0, smul_zero]

/-- The first coordinate of the approximants is that of `T`: in the setting of
`exists_analytic_approximation_of_lifting`, `ν_{Y•}(T_k)₀ = ν_{W•}(T)₀` (the generic Lelong
number along `Y₁` of the pushforwards is that of `T` along the strict transform `W₁`). -/
theorem flagValuation_zero_of_approximation {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) {ψ : W.carrier → EReal}
    {φ : F.carrier → EReal} {w : Fin (m + 1) → ℝ} (hw : w 0 = 0) {t : ℝ}
    (h : flagValuation F φ ᵥ* correctionMatrixReal hπ = flagValuation W ψ + t • w) :
    flagValuation F φ 0 = flagValuation W ψ 0 := by
  have h0 := congrFun h 0
  rw [vecMul_correctionMatrixReal_zero hπ, Pi.add_apply, Pi.smul_apply, hw, smul_zero,
    add_zero] at h0
  exact h0

/-- **Approximation for gentle Kähler currents** (the case `T ∈ Ω(W, π^*ξ)` used for the lifting
invariance), conditional on `PushforwardAnalyticStatement`. -/
theorem exists_analytic_approximation_of_gentleKahler (hP : PushforwardAnalyticStatement.{u})
    {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {ψ : W.carrier → EReal}
    (hψ : ψ ∈ gentleKahlerCurrents (ClosedRealOneOneForm.pullback hπ.1.1 θ)) :
    ∃ (w : Fin (m + 1) → ℝ) (φ : ℕ → F.carrier → EReal),
      (∀ k, φ k ∈ analyticCurrents θ) ∧
      (∀ k, flagValuation F (φ k) ᵥ* correctionMatrixReal hπ =
        flagValuation W ψ + ((1 : ℝ) / ((k : ℝ) + 1)) • w) := by
  obtain ⟨w, φ, -, hφA, -, -, hφν⟩ := exists_analytic_approximation_of_lifting hP hπ
    (gentleKahlerCurrents_subset_globalAnalyticCurrents hψ) hψ.2
  exact ⟨w, φ, hφA, hφν⟩

end SGPT.Okounkov.TranscendentalLifting

import SGPT.Envelopes.CapacityConsumersEdiff
import SGPT.Envelopes.SourceFullMassIntegralEstimates
import SGPT.PSH.SourceRayL1
import SGPT.Foundations.Analysis.Pending.NaturalThetaPshHartogsRecovery

/-!
# Stability of the relative full mass class under `L¹` limits

Source `lma:stab` (chapter `chapter_envelopes.tex`, subsection `subsec:fullmass`): let `X` be
a connected compact Kähler manifold, `θ` of big class and `ϕ` a model potential of positive
mass.  Let `φ_j, γ ∈ E(X, θ; ϕ)` with `φ_j ≤ γ`, `φ_j → φ ∈ PSH(X, θ)` in `L¹`, and assume
`∫_X (φ_j - γ) θ_{φ_j}^n ≥ -A` for all `j`.  Then `φ ∈ E(X, θ; ϕ)` and
`∫_X (φ - γ) θ_φ^n ≥ -2^{n+3} A`.

Formalization.  The integrals of the non-positive functions `φ_j - γ` are read through the
non-negative gap integrals `sourceDiagonalGapIntegral θ γ u u = ∫⁻ |γ - u| θ_u^n` (values in
`[0, ∞]`): `∫(φ_j - γ)θ_{φ_j}^n ≥ -A` is `∫⁻ (γ - φ_j) θ_{φ_j}^n ≤ A`.  `L¹` convergence is
convergence in `L¹(X, ω^n)` (`sourceGlobalL1Distance`).

Proof (the source's): Step 1 treats decreasing sequences with `lma:intdom1` and the liminf
part of `thm:semicon` (the weights `γ - max(φ_j, γ - C)` are bounded and quasi-continuous by
`ex:psh_qc`), followed by monotone convergence.  Step 2 applies Step 1 to the decreasing
regularized tails `ψ_j ∨ (γ - C)`, `ψ_j = (sup_{k ≥ j} φ_k)^*`, which decrease to `φ ∨ (γ - C)`
(`cor:L1limipp`), using `lma:fundam_estimate`, and concludes with plurifine locality, monotone
convergence and `thm:mono`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Envelopes.CapacityConsumers

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas SGPT.NPP SGPT.NPP.CapacityConvergence

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The coercion `ℝ → EReal` commutes with `max`. -/
theorem coe_max_ereal (a b : ℝ) : ((max a b : ℝ) : EReal) = max (a : EReal) (b : EReal) :=
  EReal.coe_strictMono.monotone.map_max

/-- The truncated weight `γ - max(ψ, γ - C)` (real part; `0` where `γ = -∞`). -/
def stabWeight (γ ψ : M → EReal) (C : ℝ) (x : M) : ℝ :=
  (γ x).toReal - (max (ψ x) (γ x + ((-C : ℝ) : EReal))).toReal

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The weight at a finite pair of values. -/
theorem stabWeight_coe_coe {γ ψ : M → EReal} {x : M} {g p C : ℝ} (hg : γ x = g)
    (hp : ψ x = p) : stabWeight γ ψ C x = min (g - p) C := by
  rw [stabWeight, hg, hp, ← EReal.coe_add, ← coe_max_ereal, EReal.toReal_coe,
    EReal.toReal_coe]
  rcases le_total p (g + -C) with h | h
  · rw [max_eq_right h, min_eq_right (by linarith)]; ring
  · rw [max_eq_left h, min_eq_left (by linarith)]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The weight where `ψ = -∞ < γ`. -/
theorem stabWeight_coe_bot {γ ψ : M → EReal} {x : M} {g C : ℝ} (hg : γ x = g)
    (hp : ψ x = ⊥) : stabWeight γ ψ C x = C := by
  rw [stabWeight, hg, hp, ← EReal.coe_add, max_eq_right bot_le, EReal.toReal_coe,
    EReal.toReal_coe]
  ring

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The weight where `γ = -∞`. -/
theorem stabWeight_bot {γ ψ : M → EReal} {x : M} {C : ℝ} (hg : γ x = ⊥) (hψ : ψ x ≤ γ x) :
    stabWeight γ ψ C x = 0 := by
  have hp : ψ x = ⊥ := le_bot_iff.mp (hg ▸ hψ)
  rw [stabWeight, hg, hp, EReal.bot_add, max_self]
  simp

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Bounds, comparison with the gap, and monotonicity of the weight. -/
theorem stabWeight_props {γ ψ : M → EReal} (hγt : ∀ x, γ x ≠ ⊤) (hψt : ∀ x, ψ x ≠ ⊤)
    (hψγ : ψ ≤ γ) {C : ℝ} (hC : 0 ≤ C) (x : M) :
    0 ≤ stabWeight γ ψ C x ∧ stabWeight γ ψ C x ≤ C ∧
      ENNReal.ofReal (stabWeight γ ψ C x) ≤ canonicalERealAbsDiff (γ x) (ψ x) := by
  by_cases hg : γ x = ⊥
  · rw [stabWeight_bot hg (hψγ x)]
    exact ⟨le_rfl, hC, by simp⟩
  have hgx : γ x = ((γ x).toReal : EReal) := (EReal.coe_toReal (hγt x) hg).symm
  by_cases hp : ψ x = ⊥
  · rw [stabWeight_coe_bot hgx hp]
    refine ⟨hC, le_rfl, ?_⟩
    rw [hp, hgx]
    simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff]
  have hpx : ψ x = ((ψ x).toReal : EReal) := (EReal.coe_toReal (hψt x) hp).symm
  have hle : (ψ x).toReal ≤ (γ x).toReal := EReal.toReal_le_toReal (hψγ x) hp (hγt x)
  rw [stabWeight_coe_coe hgx hpx]
  refine ⟨le_min (by linarith) hC, min_le_right _ _, ?_⟩
  rw [hgx, hpx, canonicalERealAbsDiff_coe_coe, abs_of_nonneg (by linarith)]
  exact ENNReal.ofReal_le_ofReal (min_le_left _ _)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The weight increases when `ψ` decreases and when `C` increases. -/
theorem stabWeight_mono {γ ψ ψ' : M → EReal} (hγt : ∀ x, γ x ≠ ⊤) (hψt : ∀ x, ψ x ≠ ⊤)
    (hψγ : ψ ≤ γ) (hψψ' : ψ' ≤ ψ) {C C' : ℝ} (_hC : 0 ≤ C) (hCC' : C ≤ C') (x : M) :
    stabWeight γ ψ C x ≤ stabWeight γ ψ' C' x := by
  by_cases hg : γ x = ⊥
  · rw [stabWeight_bot hg (hψγ x), stabWeight_bot hg ((hψψ' x).trans (hψγ x))]
  have hgx : γ x = ((γ x).toReal : EReal) := (EReal.coe_toReal (hγt x) hg).symm
  have hψ't : ψ' x ≠ ⊤ := ne_top_of_le_ne_top (hψt x) (hψψ' x)
  by_cases hp' : ψ' x = ⊥
  · rw [stabWeight_coe_bot hgx hp']
    by_cases hp : ψ x = ⊥
    · rw [stabWeight_coe_bot hgx hp]; exact hCC'
    · rw [stabWeight_coe_coe hgx (EReal.coe_toReal (hψt x) hp).symm]
      exact (min_le_right _ _).trans hCC'
  have hp : ψ x ≠ ⊥ := fun h => hp' (le_bot_iff.mp (h ▸ hψψ' x))
  rw [stabWeight_coe_coe hgx (EReal.coe_toReal (hψt x) hp).symm,
    stabWeight_coe_coe hgx (EReal.coe_toReal hψ't hp').symm]
  have hle : (ψ' x).toReal ≤ (ψ x).toReal := EReal.toReal_le_toReal (hψψ' x) hp' (hψt x)
  exact min_le_min (by linarith) hCC'

section Standing

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {ϕ : M → EReal}

/-- The real difference of two `θ`-psh functions is quasi-continuous for `Cap_θ`
(`ex:psh_qc`, global case). -/
theorem sourceQuasiContinuousOn_toReal_sub (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u v : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) :
    SourceQuasiContinuousOn θ ⊤ (fun x => (((u x.1).toReal - (v x.1).toReal : ℝ) : EReal)) := by
  have hqu := ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu).quasiPshPotential
  have hqv := ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv).quasiPshPotential
  have hm : Measurable fun x => (u x).toReal - (v x).toReal :=
    (measurable_of_isThetaPSH hu).ereal_toReal.sub (measurable_of_isThetaPSH hv).ereal_toReal
  refine sourceQuasiContinuousOn_of_forall θ ⊤
    ((measurable_coe_real_ereal.comp hm).comp measurable_subtype_coe) fun ε hε => ?_
  obtain ⟨G, hGo, hGc, -, hGcont⟩ :=
    exists_isOpen_sourceCapacity_le_finite_continuousOn ω θ hbig hqu (half_pos hε)
  obtain ⟨H, hHo, hHc, -, hHcont⟩ :=
    exists_isOpen_sourceCapacity_le_finite_continuousOn ω θ hbig hqv (half_pos hε)
  refine ⟨G ∪ H, hGo.union hHo, ?_, fun x => (u x).toReal - (v x).toReal, ?_, fun x _ => rfl⟩
  · calc sourceThetaCapacity θ (G ∪ H)
        ≤ sourceThetaCapacity θ G + sourceThetaCapacity θ H := sourceThetaCapacity_union_le θ G H
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hGc hHc
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
  · exact (hGcont.mono (compl_subset_compl.mpr subset_union_left)).sub
      (hHcont.mono (compl_subset_compl.mpr subset_union_right))

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- A finite translate of a source `θ`-psh function is source `θ`-psh. -/
theorem isThetaPSH_add_const {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (c : ℝ) :
    (ofFixedModel n M).IsThetaPSH θ (fun x => u x + (c : EReal)) :=
  (isThetaPSH_iff_nativeThetaPotential θ _).mpr
    (((isThetaPSH_iff_nativeThetaPotential θ u).mp hu).add_const c)

variable [ConnectedSpace M]

/-- **Step 1 of `lma:stab`** (decreasing sequences): if `ψ_k ∈ E(X,θ;ϕ)`, `ψ_k ≤ γ`,
`ψ_k` decreases to a `θ`-psh `ψ₀` and `∫⁻ (γ - ψ_k) θ_{ψ_k}^n ≤ B`, then
`∫⁻ (γ - ψ₀) θ_{ψ₀}^n ≤ 4B`. -/
theorem stab_decreasing (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hϕ : SourceModelPotential θ ϕ) {γ : M → EReal} (hγ : SourceRelativeFullMass θ ϕ γ hϕ)
    {ψ : ℕ → M → EReal} (hψ : ∀ k, SourceRelativeFullMass θ ϕ (ψ k) hϕ)
    (hψγ : ∀ k, ψ k ≤ γ) (hanti : ∀ x, Antitone fun k => ψ k x) {ψ₀ : M → EReal}
    (hψ₀ : (ofFixedModel n M).IsThetaPSH θ ψ₀)
    (hlim : ∀ x, Tendsto (fun k => ψ k x) atTop (𝓝 (ψ₀ x))) {B : ℝ≥0∞}
    (hB : ∀ k, sourceDiagonalGapIntegral θ γ (ψ k) (ψ k) (hψ k).choose ≤ B) :
    sourceDiagonalGapIntegral θ γ ψ₀ ψ₀ hψ₀ ≤ 4 * B := by
  have hγt : ∀ x, γ x ≠ ⊤ := hγ.choose.1
  have hψt : ∀ k x, ψ k x ≠ ⊤ := fun k => (hψ k).choose.1
  have hcross : ∀ j k, sourceDiagonalGapIntegral θ γ (ψ j) (ψ k) (hψ k).choose ≤ 4 * B := by
    intro j k
    refine (sourceFullMass_upper_integral_comparison ω (hψ j) (hψ k) hγ (hψγ j)
      (hψγ k)).trans ?_
    calc 2 * sourceDiagonalGapIntegral θ γ (ψ j) (ψ j) (hψ j).choose +
          2 * sourceDiagonalGapIntegral θ γ (ψ k) (ψ k) (hψ k).choose
        ≤ 2 * B + 2 * B := add_le_add (mul_le_mul' le_rfl (hB j)) (mul_le_mul' le_rfl (hB k))
      _ = 4 * B := by rw [← add_mul]; norm_num
  have hstep : ∀ (j : ℕ) (C : ℝ), 0 ≤ C →
      ∫⁻ x, ENNReal.ofReal (stabWeight γ (ψ j) C x) ∂sourcePotentialNonPluripolarMeasure θ ψ₀ hψ₀ ≤
        4 * B := by
    intro j C hC
    have hmax : (ofFixedModel n M).IsThetaPSH θ
        (fun x => max (ψ j x) (γ x + ((-C : ℝ) : EReal))) :=
      sourceThetaMaximum_genuine (hψ j).choose (isThetaPSH_add_const hγ.choose (-C))
    have hqc := sourceQuasiContinuousOn_toReal_sub ω hbig hγ.choose hmax
    have hwm : Measurable (stabWeight γ (ψ j) C) :=
      (measurable_of_isThetaPSH hγ.choose).ereal_toReal.sub
        (measurable_of_isThetaPSH hmax).ereal_toReal
    have hwb := stabWeight_props hγt (hψt j) (hψγ j) hC
    have h := sourceSemicon_liminf ω θ hbig (fun _ : Fin n => θ)
      (φ := fun k _ => ψ k) (φ₀ := fun _ => ψ₀) (fun k _ => (hψ k).choose) (fun _ => hψ₀)
      (fun _ => Or.inl ⟨hanti, hlim⟩)
      (χ := fun _ => stabWeight γ (ψ j) C) (χ₀ := stabWeight γ (ψ j) C) (C := C)
      (fun _ x => ⟨(hwb x).1, (hwb x).2.1⟩) (fun x => ⟨(hwb x).1, (hwb x).2.1⟩)
      (fun _ => hqc) hqc (sourceTendstoInCapacity_const_real θ hwm)
    refine h.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_))
    refine le_trans ?_ (hcross j k)
    exact lintegral_mono fun x => (hwb x).2.2
  -- the diagonal sequence of weights
  let F : ℕ → M → ℝ≥0∞ := fun m x => ENNReal.ofReal (stabWeight γ (ψ m) m x)
  have hFm : ∀ m, Measurable (F m) := fun m => by
    have hmax : (ofFixedModel n M).IsThetaPSH θ
        (fun x => max (ψ m x) (γ x + ((-(m : ℝ) : ℝ) : EReal))) :=
      sourceThetaMaximum_genuine (hψ m).choose (isThetaPSH_add_const hγ.choose (-(m : ℝ)))
    exact ENNReal.measurable_ofReal.comp ((measurable_of_isThetaPSH hγ.choose).ereal_toReal.sub
      (measurable_of_isThetaPSH hmax).ereal_toReal)
  have hFmono : Monotone F := by
    intro m m' hmm' x
    exact ENNReal.ofReal_le_ofReal (stabWeight_mono hγt (hψt m) (hψγ m)
      (fun y => hanti y hmm') (Nat.cast_nonneg m) (Nat.cast_le.mpr hmm') x)
  have hsup : ∀ᵐ x ∂sourcePotentialNonPluripolarMeasure θ ψ₀ hψ₀,
      ⨆ m, F m x = canonicalERealAbsDiff (γ x) (ψ₀ x) := by
    filter_upwards [ae_ne_bot_of_isThetaPSH hψ₀ hψ₀] with x hx
    have hψ₀le : ∀ k, ψ₀ x ≤ ψ k x := fun k => (hanti x).le_of_tendsto (hlim x) k
    have hψ₀t : ψ₀ x ≠ ⊤ := hψ₀.1 x
    have hkb : ∀ k, ψ k x ≠ ⊥ := fun k h => hx (le_bot_iff.mp (h ▸ hψ₀le k))
    have hgb : γ x ≠ ⊥ := fun h => hkb 0 (le_bot_iff.mp (h ▸ hψγ 0 x))
    set g := (γ x).toReal
    set p := (ψ₀ x).toReal
    have hgx : γ x = (g : EReal) := (EReal.coe_toReal (hγt x) hgb).symm
    have hpx : ψ₀ x = (p : EReal) := (EReal.coe_toReal hψ₀t hx).symm
    have hkx : ∀ k, ψ k x = ((ψ k x).toReal : EReal) := fun k =>
      (EReal.coe_toReal (hψt k x) (hkb k)).symm
    have hpk : ∀ k, p ≤ (ψ k x).toReal := fun k =>
      EReal.toReal_le_toReal (hψ₀le k) hx (hψt k x)
    have hkg : ∀ k, (ψ k x).toReal ≤ g := fun k =>
      EReal.toReal_le_toReal (hψγ k x) (hkb k) (hγt x)
    have hFx : ∀ m, F m x = ENNReal.ofReal (min (g - (ψ m x).toReal) m) := fun m => by
      simp only [F]
      rw [stabWeight_coe_coe hgx (hkx m)]
    have htarget : canonicalERealAbsDiff (γ x) (ψ₀ x) = ENNReal.ofReal (g - p) := by
      rw [hgx, hpx, canonicalERealAbsDiff_coe_coe, abs_of_nonneg (by linarith [hpk 0, hkg 0])]
    rw [htarget]
    apply le_antisymm
    · refine iSup_le fun m => ?_
      rw [hFx m]
      exact ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans (by linarith [hpk m]))
    · have hreal : Tendsto (fun k => (ψ k x).toReal) atTop (𝓝 p) :=
        (EReal.tendsto_toReal hψ₀t hx).comp (hlim x)
      have hsub : Tendsto (fun m : ℕ => g - (ψ m x).toReal) atTop (𝓝 (g - p)) :=
        tendsto_const_nhds.sub hreal
      have hmin : Tendsto (fun m : ℕ => min (g - (ψ m x).toReal) m) atTop (𝓝 (g - p)) := by
        refine hsub.congr' ?_
        filter_upwards [eventually_ge_atTop ⌈g - p⌉₊] with m hm
        refine (min_eq_left ?_).symm
        have h1 : g - (ψ m x).toReal ≤ g - p := by linarith [hpk m]
        exact h1.trans ((Nat.le_ceil _).trans (Nat.cast_le.mpr hm))
      have hF : Tendsto (fun m => F m x) atTop (𝓝 (ENNReal.ofReal (g - p))) := by
        simp only [hFx]
        exact (ENNReal.continuous_ofReal.tendsto _).comp hmin
      exact le_of_tendsto' hF fun m => le_iSup (fun m => F m x) m
  calc sourceDiagonalGapIntegral θ γ ψ₀ ψ₀ hψ₀
      = ∫⁻ x, ⨆ m, F m x ∂sourcePotentialNonPluripolarMeasure θ ψ₀ hψ₀ :=
        lintegral_congr_ae (hsup.mono fun x hx => hx.symm)
    _ = ⨆ m, ∫⁻ x, F m x ∂sourcePotentialNonPluripolarMeasure θ ψ₀ hψ₀ :=
        lintegral_iSup hFm hFmono
    _ ≤ 4 * B := iSup_le fun m => hstep m m (Nat.cast_nonneg m)

/-- **Source `lma:stab`.**  Let `φ_j, γ ∈ E(X, θ; ϕ)` with `φ_j ≤ γ`, `φ_j → φ` in
`L¹(X, ω^n)`, `φ ∈ PSH(X, θ)`, and `∫_X (φ_j - γ) θ_{φ_j}^n ≥ -A` for all `j` (read as
`∫⁻ (γ - φ_j) θ_{φ_j}^n ≤ A`).  Then `φ ∈ E(X, θ; ϕ)` and `∫_X (φ - γ) θ_φ^n ≥ -2^{n+3} A`.
(The source takes `A > 0`; the statement holds for every real `A`.) -/
theorem sourceStab (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hϕ : SourceModelPotential θ ϕ) {φs : ℕ → M → EReal} {γ φ : M → EReal}
    (hφs : ∀ j, SourceRelativeFullMass θ ϕ (φs j) hϕ) (hγ : SourceRelativeFullMass θ ϕ γ hϕ)
    (hle : ∀ j, φs j ≤ γ) (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hlim : Tendsto (fun j => sourceGlobalL1Distance ω (φs j) φ) atTop (𝓝 0))
    {A : ℝ}
    (hint : ∀ j, sourceDiagonalGapIntegral θ γ (φs j) (φs j) (hφs j).choose ≤ ENNReal.ofReal A) :
    SourceRelativeFullMass θ ϕ φ hϕ ∧
      sourceDiagonalGapIntegral θ γ φ φ hφ ≤ ENNReal.ofReal (2 ^ (n + 3) * A) := by
  set K : ℝ≥0∞ := ENNReal.ofReal (2 ^ (n + 3) * A) with hK
  have hKtop : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have hK4 : (4 : ℝ≥0∞) * (2 ^ (n + 1) * ENNReal.ofReal A) = K := by
    rw [hK, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat, ← mul_assoc]
    congr 1
    rw [show (4 : ℝ≥0∞) = 2 ^ 2 by norm_num, ← pow_add]
    ring_nf
  have hγt : ∀ x, γ x ≠ ⊤ := hγ.choose.1
  have hγN := (isThetaPSH_iff_nativeThetaPotential θ γ).mp hγ.choose
  have hφN := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ
  have hφsN := fun j => (isThetaPSH_iff_nativeThetaPotential θ (φs j)).mp (hφs j).choose
  rcases isEmpty_or_nonempty M with hM | hM
  · have hμ : ∀ (u : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u),
        sourcePotentialNonPluripolarMeasure θ u hu = 0 := fun _ _ => Measure.eq_zero_of_isEmpty _
    refine ⟨⟨hφ, ⟨0, fun x => isEmptyElim x⟩, by simp only [hμ]⟩, ?_⟩
    simp only [sourceDiagonalGapIntegral, hμ, lintegral_zero_measure, zero_le]
  -- the L¹ hypothesis in charts
  have hL1 : ManifoldL1LocallyTendsto (n := n) φs atTop φ :=
    (manifoldL1LocallyTendsto_iff_global_of_eventually_measurable
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ω)
      (Eventually.of_forall fun j => measurable_of_isThetaPSH (hφs j).choose)
      (measurable_of_isThetaPSH hφ)).mpr hlim
  obtain ⟨c₀, hc₀⟩ := hγN.exists_global_upper_bound
  obtain ⟨hψN, hψanti, hψinf, hψlim⟩ :=
    NaturalThetaPshHartogsRecovery.usc_tailSup_iInf_eq_and_tendsto hφsN hφN hL1 (C := c₀)
      (fun j x => (hle j x).trans (hc₀ x))
  set ψ : ℕ → M → EReal := fun N => uscRegularization (⨆ j : ℕ, φs (j + N)) with hψdef
  have hψ : ∀ N, (ofFixedModel n M).IsThetaPSH θ (ψ N) := fun N =>
    (isThetaPSH_iff_nativeThetaPotential θ _).mpr (hψN N)
  have hψγ : ∀ N, ψ N ≤ γ := fun N =>
    FirstPass.uscRegularization_le hγN.1.quasiPlurisubharmonic.upperSemicontinuous
      (fun x => by simpa only [iSup_apply] using iSup_le fun j => hle (j + N) x)
  have hφψ : ∀ N, φs N ≤ ψ N := fun N x => by
    refine le_trans ?_ (FirstPass.le_uscRegularization _ x)
    simp only [iSup_apply]
    simpa only [zero_add] using le_iSup (fun j => φs (j + N) x) 0
  have hφγ : φ ≤ γ := fun x => by
    have h := congrFun hψinf x
    simp only [iInf_apply] at h
    rw [← h]
    exact (iInf_le (fun N => ψ N x) 0).trans (hψγ 0 x)
  have hφϕ : SGPT.PSH.SingularityLE φ ϕ :=
    SGPT.PSH.singularityLE_trans (MoreSingularOn.of_le fun x _ => hφγ x) hγ.choose_spec.1
  -- Step 2: the truncated tails
  have hgapC : ∀ C : ℕ, ∀ hφC : (ofFixedModel n M).IsThetaPSH θ
      (fun x => max (φ x) (γ x + ((-(C : ℝ) : ℝ) : EReal))),
      sourceDiagonalGapIntegral θ γ (fun x => max (φ x) (γ x + ((-(C : ℝ) : ℝ) : EReal)))
        (fun x => max (φ x) (γ x + ((-(C : ℝ) : ℝ) : EReal))) hφC ≤ K := by
    intro C hφC
    set c : ℝ := (C : ℝ)
    have hγC := sourceRelativeFullMass_add_const hγ (-c)
    have hψC : ∀ N, SourceRelativeFullMass θ ϕ
        (fun x => max (ψ N x) (γ x + ((-c : ℝ) : EReal))) hϕ := by
      intro N
      have hpsh := sourceThetaMaximum_genuine (hψ N) hγC.choose
      have hle' : (fun x => max (ψ N x) (γ x + ((-c : ℝ) : EReal))) ≤ γ := fun x =>
        max_le (hψγ N x) (add_le_of_nonpos_right (EReal.coe_nonpos.mpr (by
          simp only [c, neg_nonpos]; exact Nat.cast_nonneg C)))
      exact sourceRelativeFullMass_upward ω hγC
        ⟨hpsh, SGPT.PSH.singularityLE_trans (MoreSingularOn.of_le fun x _ => hle' x)
          hγ.choose_spec.1⟩ (MoreSingularOn.of_le fun x _ => le_max_right _ _)
    have hψCγ : ∀ N, (fun x => max (ψ N x) (γ x + ((-c : ℝ) : EReal))) ≤ γ := fun N x =>
      max_le (hψγ N x) (add_le_of_nonpos_right (EReal.coe_nonpos.mpr (by
        simp only [c, neg_nonpos]; exact Nat.cast_nonneg C)))
    have hB : ∀ N, sourceDiagonalGapIntegral θ γ
        (fun x => max (ψ N x) (γ x + ((-c : ℝ) : EReal)))
        (fun x => max (ψ N x) (γ x + ((-c : ℝ) : EReal))) (hψC N).choose ≤
          2 ^ (n + 1) * ENNReal.ofReal A := fun N =>
      (sourceFullMass_fundamental_integral_estimate ω (hφs N) (hψC N) hγ
        (fun x => (hφψ N x).trans (le_max_left _ _)) (hψCγ N)).trans
        (mul_le_mul' le_rfl (hint N))
    have h1 := stab_decreasing ω hbig hϕ hγ hψC hψCγ
      (fun x N L hNL => max_le_max (hψanti hNL x) le_rfl) hφC
      (fun x => (hψlim x).max tendsto_const_nhds) hB
    rwa [hK4] at h1
  -- locality on `{φ > γ - C}`
  have hloc : ∀ C : ℕ, ∀ hφC : (ofFixedModel n M).IsThetaPSH θ
      (fun x => max (φ x) (γ x + ((-(C : ℝ) : ℝ) : EReal))),
      (sourcePotentialNonPluripolarMeasure θ _ hφC).restrict
          {x | γ x + ((-(C : ℝ) : ℝ) : EReal) < φ x} =
        (sourcePotentialNonPluripolarMeasure θ φ hφ).restrict
          {x | γ x + ((-(C : ℝ) : ℝ) : EReal) < φ x} := by
    intro C hφC
    have hγCN := (isThetaPSH_iff_nativeThetaPotential θ _).mp
      (isThetaPSH_add_const hγ.choose (-(C : ℝ)))
    have h := GlobalMaxLocality.globalMixedMeasure_restrict_max_eq
      (θ := fun _ : Fin n => atlasClosedFormToNative θ)
      (u := fun _ => φ) (w := fun _ => fun x => γ x + ((-(C : ℝ) : ℝ) : EReal))
      (fun _ => hφN.1) (fun _ => hγCN.1)
      (fun _ => ((isThetaPSH_iff_nativeThetaPotential θ _).mp hφC).1)
    have hO : MeasurableSet {x | γ x + ((-(C : ℝ) : ℝ) : EReal) < φ x} :=
      measurableSet_lt (measurable_of_isThetaPSH (isThetaPSH_add_const hγ.choose (-(C : ℝ))))
        (measurable_of_isThetaPSH hφ)
    have hsub : {x | γ x + ((-(C : ℝ) : ℝ) : EReal) < φ x} ⊆
        {x | ∀ _i : Fin n, γ x + ((-(C : ℝ) : ℝ) : EReal) < φ x} := fun x hx _ => hx
    have h' := congrArg (fun μ : Measure M =>
      μ.restrict {x | γ x + ((-(C : ℝ) : ℝ) : EReal) < φ x}) h
    simp only [Measure.restrict_restrict hO, inter_eq_left.mpr hsub] at h'
    exact h'
  have hφCpsh : ∀ C : ℕ, (ofFixedModel n M).IsThetaPSH θ
      (fun x => max (φ x) (γ x + ((-(C : ℝ) : ℝ) : EReal))) := fun C =>
    sourceThetaMaximum_genuine hφ (isThetaPSH_add_const hγ.choose (-(C : ℝ)))
  have hOm : ∀ C : ℕ, MeasurableSet {x | γ x + ((-(C : ℝ) : ℝ) : EReal) < φ x} := fun C =>
    measurableSet_lt (measurable_of_isThetaPSH (isThetaPSH_add_const hγ.choose (-(C : ℝ))))
      (measurable_of_isThetaPSH hφ)
  set f : M → ℝ≥0∞ := fun x => canonicalERealAbsDiff (γ x) (φ x) with hfdef
  have hfm : Measurable f :=
    (measurable_of_isThetaPSH hγ.choose).canonicalERealAbsDiff (measurable_of_isThetaPSH hφ)
  -- integral on `{φ > γ - C}`
  have hpiece : ∀ C : ℕ, ∫⁻ x in {x | γ x + ((-(C : ℝ) : ℝ) : EReal) < φ x}, f x
      ∂sourcePotentialNonPluripolarMeasure θ φ hφ ≤ K := by
    intro C
    rw [← hloc C (hφCpsh C)]
    refine le_trans ?_ (hgapC C (hφCpsh C))
    rw [setLIntegral_congr_fun (hOm C) (g := fun x => canonicalERealAbsDiff (γ x)
      (max (φ x) (γ x + ((-(C : ℝ) : ℝ) : EReal)))) (fun x hx => by
        simp only [f]
        rw [max_eq_left (le_of_lt (show γ x + ((-(C : ℝ) : ℝ) : EReal) < φ x from hx))])]
    exact setLIntegral_le_lintegral _ _
  -- monotone exhaustion
  have hmonoO : Monotone fun C : ℕ => {x | γ x + ((-(C : ℝ) : ℝ) : EReal) < φ x} := by
    intro C C' hCC' x hx
    refine lt_of_le_of_lt (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_)) hx
    simp only [neg_le_neg_iff, Nat.cast_le]; exact hCC'
  have hexh : ∀ᵐ x ∂sourcePotentialNonPluripolarMeasure θ φ hφ,
      ⨆ C : ℕ, {x | γ x + ((-(C : ℝ) : ℝ) : EReal) < φ x}.indicator f x = f x := by
    filter_upwards [ae_ne_bot_of_isThetaPSH hφ hφ] with x hx
    have hgb : γ x ≠ ⊥ := fun h => hx (le_bot_iff.mp (h ▸ hφγ x))
    obtain ⟨C, hC⟩ := exists_nat_gt ((γ x).toReal - (φ x).toReal)
    have hmem : x ∈ {x | γ x + ((-(C : ℝ) : ℝ) : EReal) < φ x} := by
      change γ x + ((-(C : ℝ) : ℝ) : EReal) < φ x
      rw [← EReal.coe_toReal (hγt x) hgb, ← EReal.coe_toReal (hφ.1 x) hx, ← EReal.coe_add,
        EReal.coe_lt_coe_iff]
      linarith
    apply le_antisymm
    · exact iSup_le fun C' => indicator_le_self _ _ x
    · exact le_iSup_of_le C (by rw [indicator_of_mem hmem])
  have hint' : sourceDiagonalGapIntegral θ γ φ φ hφ ≤ K := by
    calc sourceDiagonalGapIntegral θ γ φ φ hφ
        = ∫⁻ x, ⨆ C : ℕ, {x | γ x + ((-(C : ℝ) : ℝ) : EReal) < φ x}.indicator f x
            ∂sourcePotentialNonPluripolarMeasure θ φ hφ :=
          lintegral_congr_ae (hexh.mono fun x hx => hx.symm)
      _ = ⨆ C : ℕ, ∫⁻ x, {x | γ x + ((-(C : ℝ) : ℝ) : EReal) < φ x}.indicator f x
            ∂sourcePotentialNonPluripolarMeasure θ φ hφ :=
          lintegral_iSup (fun C => hfm.indicator (hOm C))
            (fun C C' hCC' => indicator_le_indicator_of_subset (hmonoO hCC') (fun _ => zero_le))
      _ ≤ K := iSup_le fun C => by rw [lintegral_indicator (hOm C)]; exact hpiece C
  -- full mass
  have hmass_le : sourcePotentialNonPluripolarMeasure θ φ hφ univ ≤
      sourcePotentialNonPluripolarMeasure θ ϕ hϕ.thetaPSH univ :=
    sourcePotentialNonPluripolarMass_mono ω hφ hϕ.thetaPSH hφϕ
  have hmass_ge : sourcePotentialNonPluripolarMeasure θ ϕ hϕ.thetaPSH univ ≤
      sourcePotentialNonPluripolarMeasure θ φ hφ univ := by
    have hbound : ∀ C : ℕ, sourcePotentialNonPluripolarMeasure θ ϕ hϕ.thetaPSH univ ≤
        sourcePotentialNonPluripolarMeasure θ φ hφ univ +
          sourcePotentialNonPluripolarMeasure θ _ (hφCpsh C)
            {x | γ x + ((-(C : ℝ) : ℝ) : EReal) < φ x}ᶜ ∧
        (C : ℝ≥0∞) * sourcePotentialNonPluripolarMeasure θ _ (hφCpsh C)
            {x | γ x + ((-(C : ℝ) : ℝ) : EReal) < φ x}ᶜ ≤ K := by
      intro C
      set O := {x | γ x + ((-(C : ℝ) : ℝ) : EReal) < φ x}
      set μC := sourcePotentialNonPluripolarMeasure θ _ (hφCpsh C)
      have hγC := sourceRelativeFullMass_add_const hγ (-(C : ℝ))
      have hfullC : SourceRelativeFullMass θ ϕ
          (fun x => max (φ x) (γ x + ((-(C : ℝ) : ℝ) : EReal))) hϕ :=
        sourceRelativeFullMass_upward ω hγC
          ⟨hφCpsh C, SGPT.PSH.singularityLE_trans (MoreSingularOn.of_le fun x _ =>
            max_le (hφγ x) (add_le_of_nonpos_right (EReal.coe_nonpos.mpr (by
              simp only [neg_nonpos]; exact Nat.cast_nonneg C)))) hγ.choose_spec.1⟩
          (MoreSingularOn.of_le fun x _ => le_max_right _ _)
      have hmC : μC univ = sourcePotentialNonPluripolarMeasure θ ϕ hϕ.thetaPSH univ :=
        hfullC.choose_spec.2
      have hOeq : μC O = sourcePotentialNonPluripolarMeasure θ φ hφ O := by
        have h := congrArg (fun μ : Measure M => μ univ) (hloc C (hφCpsh C))
        simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter] using h
      constructor
      · rw [← hmC, ← measure_add_measure_compl (hOm C), hOeq]
        exact add_le_add (measure_mono (subset_univ _)) le_rfl
      · have hae : Oᶜ ≤ᵐ[μC] {x | (C : ℝ≥0∞) ≤ canonicalERealAbsDiff (γ x)
            (max (φ x) (γ x + ((-(C : ℝ) : ℝ) : EReal)))} := by
          filter_upwards [ae_ne_bot_of_isThetaPSH (hφCpsh C) hγ.choose] with x hgb hxO
          have hxO' : φ x ≤ γ x + ((-(C : ℝ) : ℝ) : EReal) := not_lt.mp hxO
          change (C : ℝ≥0∞) ≤ canonicalERealAbsDiff (γ x)
            (max (φ x) (γ x + ((-(C : ℝ) : ℝ) : EReal)))
          rw [max_eq_right hxO', ← EReal.coe_toReal (hγt x) hgb, ← EReal.coe_add,
            canonicalERealAbsDiff_coe_coe]
          rw [show (γ x).toReal - ((γ x).toReal + -(C : ℝ)) = (C : ℝ) by ring,
            abs_of_nonneg (Nat.cast_nonneg C), ENNReal.ofReal_natCast]
        have hmark := mul_meas_ge_le_lintegral₀ (μ := μC)
          ((measurable_of_isThetaPSH hγ.choose).canonicalERealAbsDiff
            (measurable_of_isThetaPSH (hφCpsh C))).aemeasurable (C : ℝ≥0∞)
        exact (mul_le_mul' le_rfl (measure_mono_ae hae)).trans (hmark.trans (hgapC C (hφCpsh C)))
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hεne : (ε : ℝ≥0∞) ≠ 0 := by exact_mod_cast hε.ne'
    obtain ⟨C, hC⟩ := ENNReal.exists_nat_gt (ENNReal.div_lt_top hKtop hεne).ne
    have hKC : K < (C : ℝ≥0∞) * ε := (ENNReal.div_lt_iff (Or.inl hεne)
      (Or.inl ENNReal.coe_ne_top)).mp hC
    obtain ⟨h1, h2⟩ := hbound C
    refine h1.trans (add_le_add le_rfl ?_)
    by_contra hlt
    exact (not_le.mpr hKC) ((mul_le_mul' le_rfl (le_of_lt (not_le.mp hlt))).trans h2)
  exact ⟨⟨hφ, hφϕ, le_antisymm hmass_le hmass_ge⟩, hint'⟩

end Standing

end SGPT.Envelopes.CapacityConsumers

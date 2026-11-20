import SGPT.Foundations.Analysis.Pending.PositiveCurrentAssembly
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly
import SGPT.Foundations.Analysis.Pending.BlowupSequencePotentialDescent
import SGPT.Foundations.Analysis.Pending.StrictTransformComposition
import SGPT.Foundations.Analysis.Pending.ResidualNefReduction
import SGPT.Foundations.Analysis.Pending.MeteredDivisorPositivity
import SGPT.Foundations.Analysis.Pending.ManifoldPluripolar
import SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.Pending.ThetaPshAntitoneSupNondegenerate
import SGPT.Foundations.Analysis.Pending.DecreasingRooftopTailEnvelope
import SGPT.Foundations.Analysis.Pending.IEnvelopeOrder
import SGPT.Foundations.Analysis.Pending.IEnvelopeStrongOpenness
import SGPT.Foundations.Analysis.Pending.AmbientConvexCurrent
import SGPT.Foundations.Analysis.Pending.GlobalNonPluripolarKahler

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 `lem:domination`: the route-independent steps

Source: Copy-4, `lem:domination`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:654-812`).
The statement is fixed in `PositiveCurrentAssembly.DominationLemma`; this module proves the steps
of its proof which do not depend on the pending choices D1 (Xiao's bigness criterion,
`thm:nef-difference`) and D2 (how `S_v ≼_I v` is obtained in Step 3), in the order of the proof
(plan `scratch/tn23-envelopes-qea-plan-0117.md` §7).

## Step 1 (`eq:dom-mass`)

For `v ∈ PSH(Z, γ_η)` with `∫(γ_η)_v^k ≥ h₀`, Demailly's quasi-equisingular approximation
`v_j ∈ PSH(Z, γ_η + ε_j ω)` (global type `(2^{-j}, 𝓘(2^j v))`, `ε_j > 0`) satisfies
`∫(γ_η + ε_j ω)_{v_j}^k ≥ ∫(γ_η)_v^k ≥ h₀` for EVERY `j`: monotonicity of the mass in the
background (`AmbientMassBackgroundMonotone`) and in the singularity type
(`SingularityEnvelopeMassProof.diagonalPotentialMass_mono_of_kahler`, `v ≤ v_j`).  This is
`diagonalPotentialMass_le_of_le_add_smul` and `exists_dominationApproximation`.

## Step 3, descent (`S_j ≼_I v_j`)

Step 2 produces, on a log resolution `π : Y → Z` of `v_j` (a blowup sequence), a metered effective
`ℚ`-divisor `F` along which `π^*v_j` has log singularities (Siu decomposition, `R_j` with bounded
potentials) and a current `L_j + δπ^*ω` in the residual class, i.e. a potential
`ℓ ∈ PSH(Y, π^*(γ_η - δω) - Θ_F)`.  `exists_le_add_of_logSingularitiesAlong` descends
`S̃_j = π^*(γ_η - δω) + ddᶜ(ψ_F + ℓ)` along `π` (Xia SGPT Prop. 1.5.3,
`BlowupSequencePotentialDescent`) and gives `s_j ∈ PSH(Z, γ_η - δω)` with `s_j ≤ v_j + C_j`
EVERYWHERE, by surjectivity of `π`; hence `S_j ≼_I v_j` without Xia Prop. 6.1.2 or Lemma 6.1.4.

## Step 3, the limit

`exists_tailLimit`: for potentials `s_j ∈ PSH(Z, θ')`, `θ' = γ_η - δω`, sup-normalized to
`ŝ_j = s_j - max s_j`, the decreasing limit `s_∞` of the tail upper envelopes
`(sup_{j ≥ m} ŝ_j)^*` is a `θ'`-psh potential (so `S_v = γ_η + ddᶜs_∞ ≥ δω`).  This replaces
Copy-4's `L¹` limit of a subsequence ("weak compactness", not in the tree); what `S_v ≼_I v`
needs from the limit depends on decision D2 and is not proved here.

## `lem:domination` for a big class (`dominationLemma_of_isBigClass`)

Copy-4 states `lem:domination` for a class `{γ}` which is BIG.  Under that hypothesis the lemma has
a direct proof which uses neither Steps 2–3 (log resolution, Xiao's criterion `thm:nef-difference`,
the limit and `S_v ≼_I v`) nor any divisor over `Z`: with a Kähler current `γ + ddᶜu₀ ≥ δ₀ω` and a
uniform bound `M` for the masses in the classes `γ_η`, `η ≤ 1`, pick `a > 1` with
`(a^k - 1)M < h₀`; DDNL Lemma 4.3 (= Xia SGPT Lemma 2.4.4, big-class form, proved in
`PositiveCurrentRooftop`) applied to `v ≤ ψ := max(v, u₀)` gives `w ∈ PSH(Z, γ_η)` with
`a⁻¹w + (1 - a⁻¹)ψ ≤ v`, and `s := a⁻¹w + (1 - a⁻¹)u₀ ∈ PSH(Z, γ_η - (1 - a⁻¹)δ₀ω)` satisfies
`s ≤ v` everywhere.  So `δ_* = (1 - a⁻¹)δ₀` and `S_v ≼_I v` holds pointwise.  Copy-4 obtains the
bigness of `{γ} = α|_V` from the positivity of the restricted volume (`sec:npp`, `it:bigness`).

Sorry-free.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.DivisorialDomination

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicIdealSheaves
  FirstPass.GlobalAnalyticSingularities FirstPass.QuasiEquisingularApproximation
  FirstPass.IEnvelope DiagonalMass

/-! ### Step 1: the approximation and `eq:dom-mass` -/

section StepOne

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z] [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z]

/-- **`eq:dom-mass`, one term.**  If `v ∈ PSH(Z, θ)`, `w ∈ PSH(Z, θ + εω)`, `ε > 0` and `v ≤ w`,
then `∫θ_v^k ≤ ∫(θ + εω)_w^k`: enlarge the background (the mass does not decrease), then compare
`v ≤ w` in the common background (monotonicity of the non-pluripolar mass). -/
theorem diagonalPotentialMass_le_of_le_add_smul (omegaZ : KahlerBackground k Z)
    {θ : ClosedRealOneOneForm k Z} {ε : ℝ} (hε : 0 < ε) {v w : Z → EReal}
    (hv : IsThetaPshPotential θ.val v) (hw : IsThetaPshPotential (θ + ε • omegaZ.form).val w)
    (hvw : v ≤ w) :
    diagonalPotentialMass θ v hv ≤ diagonalPotentialMass (θ + ε • omegaZ.form) w hw := by
  have hsemi : (ε • omegaZ.form).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul omegaZ.isSemipositive hε.le
  have hv' : IsThetaPshPotential (θ + ε • omegaZ.form).val v :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hv hsemi
  calc diagonalPotentialMass θ v hv
      ≤ diagonalPotentialMass (θ + ε • omegaZ.form) v hv' :=
        AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul omegaZ.isSemipositive
          hε hv hv'
    _ ≤ diagonalPotentialMass (θ + ε • omegaZ.form) w hw :=
        diagonalPotentialMass_mono_of_kahler omegaZ hv' hw
          (MoreSingularOn.of_le fun x _ => hvw x)

/-- The terms of a pointwise decreasing sequence dominate its limit. -/
theorem le_of_decreasesPointwiseTo {vSeq : ℕ → Z → EReal} {v : Z → EReal}
    (h : DecreasesPointwiseTo vSeq v) (j : ℕ) : v ≤ vSeq j := fun x =>
  (h.1 x).le_of_tendsto (h.2 x) j

/-- **Copy-4 `lem:domination`, Step 1** (with `θ = γ_η = γ + ηω`): Demailly's quasi-equisingular
approximation `v_j` of `v` — `v_j ∈ PSH(Z, θ + ε_jω)` with `ε_j > 0`, `ε_j ↓ 0`, `v_j ↘ v`, of
global type `(2^{-j}, 𝓘(2^j v))` — satisfies `eq:dom-mass`: `h₀ ≤ ∫(θ + ε_jω)_{v_j}^k` for every
`j` as soon as `h₀ ≤ ∫θ_v^k`. -/
theorem exists_dominationApproximation (hk : 0 < k) (omegaZ : KahlerBackground k Z)
    {θ : ClosedRealOneOneForm k Z} {v : Z → EReal} (hv : IsThetaPshPotential θ.val v)
    {h₀ : ℝ≥0∞} (hmass : h₀ ≤ diagonalPotentialMass θ v hv) :
    ∃ (ε : ℕ → ℝ) (vSeq : ℕ → Z → EReal),
      IsQuasiEquisingularApproximation omegaZ θ v ε vSeq ∧ (∀ j, 0 < ε j) ∧
      (∀ j, HasAnalyticSingularitiesOfType (n := k) (vSeq j) (((2 ^ j : ℕ) : ℚ)⁻¹)
        (multiplierIdeal (n := k) ((2 ^ j : ℕ) : ℝ) v)) ∧
      (∀ j, v ≤ vSeq j) ∧
      ∀ j (hj : IsThetaPshPotential (θ + ε j • omegaZ.form).val (vSeq j)),
        h₀ ≤ diagonalPotentialMass (θ + ε j • omegaZ.form) (vSeq j) hj := by
  obtain ⟨ε, vSeq, hQ, hε, htype⟩ :=
    QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation_ofType_pos hk
      omegaZ θ hv
  have hle : ∀ j, v ≤ vSeq j := le_of_decreasesPointwiseTo hQ.2.2.2.2.1
  exact ⟨ε, vSeq, hQ, hε, htype, hle, fun j hj =>
    hmass.trans (diagonalPotentialMass_le_of_le_add_smul omegaZ (hε j) hv hj (hle j))⟩

end StepOne

/-! ### Step 3, descent: the current `S_j` on `Z` and `S_j ≼_I v_j` -/

section Descent

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

open FirstPass.BlowupSequences

/-- **Descent with a pointwise bound** (Copy-4 `lem:domination` Step 3, first half).  If
`π : Y → X` is a blowup sequence, `w ∈ PSH(Y, π^*θ)` and `w ≤ v ∘ π + C` on `Y`, then the descended
potential `s ∈ PSH(X, θ)` (`s ∘ π = w`, Xia SGPT Prop. 1.5.3) satisfies `s ≤ v + C` on `X`, by
surjectivity of `π`.  No bimeromorphic invariance of `≼_I` (Xia Lemma 6.1.4) is needed. -/
theorem exists_le_add_of_isBlowupSequence {π : Y → X} (hπ : IsBlowupSequence n X Y π)
    (θ : ClosedRealOneOneForm n X) {w : Y → EReal}
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.contMDiff θ).val w)
    {v : X → EReal} {C : ℝ} (hwv : ∀ y, w y ≤ v (π y) + (C : EReal)) :
    ∃ s : X → EReal, IsThetaPshPotential θ.val s ∧ (∀ y, s (π y) = w y) ∧
      ∀ x, s x ≤ v x + (C : EReal) := by
  obtain ⟨s, hs, hsw⟩ :=
    BlowupSequencePotentialDescent.exists_descent_of_isBlowupSequence hπ θ hw
  refine ⟨s, hs, hsw, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hπ).2 x
  rw [hsw y]
  exact hwv y

/-- The weight of a metered effective `ℚ`-divisor plus a potential of the residual class is a
potential of the full class: `ψ_F ∈ PSH(Y, Θ_F)` (`[F] = Θ_F + ddᶜψ_F ≥ 0`) and
`ℓ ∈ PSH(Y, ϑ - Θ_F)` give `ψ_F + ℓ ∈ PSH(Y, ϑ)`; poles stay pluripolar. -/
theorem isThetaPshPotential_weight_add (F : MeteredEffectiveQDivisor n Y)
    (hF : LocallyNondegenerate F.weight) {ϑ : ClosedRealOneOneForm n Y} {ℓ : Y → EReal}
    (hℓ : IsThetaPshPotential (ϑ - F.curvature).val ℓ) :
    IsThetaPshPotential ϑ.val (fun y => F.weight y + ℓ y) := by
  have hpsh := FirstPass.LocalPotentials.thetaPlurisubharmonic_add
    (MeteredDivisorPositivity.thetaPlurisubharmonic_weight F) hℓ.1
  rw [add_sub_cancel] at hpsh
  refine ⟨hpsh, ThetaPshConvexCombination.locallyNondegenerate_of_poles_pluripolar (n := n) ?_⟩
  have hFq : IsGlobalQuasiPshPotential (n := n) F.weight :=
    ⟨(MeteredDivisorPositivity.thetaPlurisubharmonic_weight F).quasiPlurisubharmonic, hF⟩
  have hℓq : IsGlobalQuasiPshPotential (n := n) ℓ := ⟨hℓ.1.quasiPlurisubharmonic, hℓ.2⟩
  refine (manifoldLocallyPluripolar_union (quasiPsh_poles_manifoldLocallyPluripolar hFq)
    (quasiPsh_poles_manifoldLocallyPluripolar hℓq)).mono fun y hy => ?_
  have hy' : F.weight y + ℓ y = ⊥ := hy
  rcases EReal.add_eq_bot_iff.mp hy' with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **Copy-4 `lem:domination` Step 3, `S_j ≼_I v_j` pointwise.**  Let `π : Y → X` be a blowup
sequence (the log resolution of Step 2), `F` a metered effective `ℚ`-divisor on `Y` such that
`π^*v` has log singularities along `F` (the Siu decomposition `π^*(θ_v) = R + [F]`, `R` with
bounded potentials), and `ℓ ∈ PSH(Y, π^*θ - Θ_F)` (the current `L + δπ^*ω` of Step 2, written
relative to `π^*θ - Θ_F`).  Then `S̃ = π^*θ + ddᶜ(ψ_F + ℓ) = [F] + (π^*θ - Θ_F + ddᶜℓ) ≥ [F]`
descends: there is `s ∈ PSH(X, θ)` with `s ∘ π = ψ_F + ℓ` and `s ≤ v + C` on `X`; in particular
`s ≼_I v` (`exists_iOrder_of_logSingularitiesAlong`).  The bound is `ψ_F ≤ π^*v + sup|b|` and
`ℓ ≤ sup ℓ`. -/
theorem exists_le_add_of_logSingularitiesAlong [Nonempty X] {π : Y → X}
    (hπ : IsBlowupSequence n X Y π) (θ : ClosedRealOneOneForm n X) {v : X → EReal}
    (F : MeteredEffectiveQDivisor n Y)
    (L : ResidualNefReduction.HasLogSingularitiesAlong F (fun y => v (π y)))
    (hv : LocallyNondegenerate (fun y => v (π y))) {ℓ : Y → EReal}
    (hℓ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.contMDiff θ - F.curvature).val ℓ) :
    ∃ s : X → EReal, IsThetaPshPotential θ.val s ∧ (∀ y, s (π y) = F.weight y + ℓ y) ∧
      ∃ C : ℝ, ∀ x, s x ≤ v x + (C : EReal) := by
  have hYc := StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hπ
  have : CompactSpace Y := hYc.1
  have : Nonempty Y := by
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨y, -⟩ := hYc.2 x
    exact ⟨y⟩
  -- `ψ_F` is finite wherever `π^*v` is
  have hF : LocallyNondegenerate F.weight := by
    intro y U hU hyU
    obtain ⟨y', hy'U, hy'⟩ := hv y U hU hyU
    refine ⟨y', hy'U, fun hbot => hy' ?_⟩
    change v (π y') = ⊥
    rw [L.weight_add y', hbot, EReal.bot_add]
  have hw := isThetaPshPotential_weight_add F hF hℓ
  obtain ⟨A, hA⟩ := hℓ.exists_global_upper_bound
  refine (exists_le_add_of_isBlowupSequence hπ θ hw (v := v) (C := L.bound + A) fun y => ?_).imp
    fun s hs => ⟨hs.1, hs.2.1, _, hs.2.2⟩
  -- `ψ_F ≤ π^*v + bound`: `π^*v = ψ_F + b` with `b ≥ -bound`
  have hb : F.weight y ≤ v (π y) + (L.bound : EReal) := by
    rw [L.weight_add y, add_assoc, ← EReal.coe_add]
    exact le_add_of_nonneg_right (EReal.coe_nonneg.mpr (by linarith [L.neg_bound_le y]))
  calc F.weight y + ℓ y ≤ (v (π y) + (L.bound : EReal)) + (A : EReal) := add_le_add hb (hA y)
    _ = v (π y) + ((L.bound + A : ℝ) : EReal) := by rw [add_assoc, ← EReal.coe_add]

/-- `exists_le_add_of_logSingularitiesAlong` with the conclusion `S_j ≼_I v_j`. -/
theorem exists_iOrder_of_logSingularitiesAlong [Nonempty X] {π : Y → X}
    (hπ : IsBlowupSequence n X Y π) (θ : ClosedRealOneOneForm n X) {v : X → EReal}
    (hvq : ManifoldQuasiPlurisubharmonic (n := n) v)
    (F : MeteredEffectiveQDivisor n Y)
    (L : ResidualNefReduction.HasLogSingularitiesAlong F (fun y => v (π y)))
    (hv : LocallyNondegenerate (fun y => v (π y))) {ℓ : Y → EReal}
    (hℓ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.contMDiff θ - F.curvature).val ℓ) :
    ∃ s : X → EReal, IsThetaPshPotential θ.val s ∧ (∀ y, s (π y) = F.weight y + ℓ y) ∧
      IOrderOnManifold (n := n) s v := by
  obtain ⟨s, hs, hsw, C, hC⟩ := exists_le_add_of_logSingularitiesAlong hπ θ F L hv hℓ
  exact ⟨s, hs, hsw, iOrderOnManifold_of_le_add hvq hC⟩

end Descent

/-! ### Step 3, the limit: tail upper envelopes of the sup-normalized `s_j` -/

section TailLimit

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z] [CompactSpace Z] [Nonempty Z]

open DecreasingRooftopTailEnvelope

/-- A potential on a nonempty compact manifold attains a finite maximum. -/
theorem exists_eq_max_of_isThetaPshPotential {θ : SmoothRealForm k Z 2} {s : Z → EReal}
    (hs : IsThetaPshPotential θ s) : ∃ c : ℝ, (∀ x, s x ≤ (c : EReal)) ∧ ∃ x, s x = (c : EReal) := by
  obtain ⟨y, -, hmax⟩ := (hs.1.quasiPlurisubharmonic.upperSemicontinuous.upperSemicontinuousOn
    univ).exists_isMaxOn univ_nonempty isCompact_univ
  obtain ⟨x₀, -, hx₀⟩ := hs.2 y univ isOpen_univ (mem_univ y)
  have hbot : s y ≠ ⊥ := fun h => hx₀ (le_bot_iff.mp (h ▸ hmax (mem_univ x₀)))
  have htop : s y ≠ ⊤ := hs.1.quasiPlurisubharmonic.ne_top y
  refine ⟨(s y).toReal, fun x => ?_, y, (EReal.coe_toReal htop hbot).symm⟩
  rw [EReal.coe_toReal htop hbot]
  exact hmax (mem_univ x)

/-- **The limit potential of Copy-4 `lem:domination` Step 3** (sup-normalized `s_j`, then a
limit).  For `θ`-psh potentials `s_j` on a compact connected `Z`, put `c_j := max s_j` and
`ŝ_j := s_j - c_j` (so `ŝ_j ≤ 0 = max ŝ_j`).  The decreasing limit
`s_∞ := lim_m (sup_{j ≥ m} ŝ_j)^*` of the tail upper envelopes (Xia SGPT Cor. 2.4.2) is a `θ`-psh
POTENTIAL — not identically `-∞`, by the Hartogs-type compactness
`ThetaPshAntitoneSupNondegenerate` — and lies below every tail envelope.  With `θ = γ_η - δω` this
is `S_v = γ_η + ddᶜs_∞ ≥ δω`.  Copy-4 takes instead an `L¹` limit of a subsequence; the tail
envelopes carry the property the divisorial-Lelong variant of `S_v ≼_I v` uses
(`ν(s_∞, ·) ≥ ν(tail envelope, ·)`, and `ŝ_j ≤ 0` uniformly). -/
theorem exists_tailLimit [ConnectedSpace Z] {θ : ClosedRealOneOneForm k Z} {s : ℕ → Z → EReal}
    (hs : ∀ j, IsThetaPshPotential θ.val (s j)) :
    ∃ c : ℕ → ℝ, (∀ j x, s j x ≤ (c j : EReal)) ∧ (∀ j, ∃ x, s j x = (c j : EReal)) ∧
      IsThetaPshPotential θ.val
        (fun x => ⨅ m, tailEnvelope (fun j y => s j y - (c j : EReal)) m x) ∧
      (∀ m, tailEnvelope (fun j y => s j y - (c j : EReal)) m ≤ 0) := by
  choose c hc hcx using fun j => exists_eq_max_of_isThetaPshPotential (hs j)
  set ŝ : ℕ → Z → EReal := fun j y => s j y - (c j : EReal) with hŝ
  have hŝpsh : ∀ j, IsThetaPshPotential θ.val (ŝ j) := fun j => (hs j).sub_const (c j)
  have hŝ0 : ∀ j, ŝ j ≤ 0 := fun j => sub_const_nonpositive_of_le (hc j)
  have hlocal : HasSmoothLocalPotentials θ.val := (hs 0).1.hasSmoothLocalPotentials
  have htail : ∀ m, IsThetaPshPotential θ.val (tailEnvelope ŝ m) :=
    isThetaPshPotential_tailEnvelope hlocal hŝpsh hŝ0
  have hanti : ∀ x, Antitone fun m => tailEnvelope ŝ m x := fun x _ _ hml =>
    tailEnvelope_antitone ŝ hml x
  -- every tail envelope reaches `0` at the maximum point of its first term
  have hreach : ∀ m, ∃ x, ((-0 : ℝ) : EReal) ≤ tailEnvelope ŝ m x := fun m => by
    obtain ⟨x, hx⟩ := hcx m
    refine ⟨x, le_trans ?_ (le_tailEnvelope_self ŝ m x)⟩
    simp only [hŝ, hx, neg_zero, EReal.coe_zero]
    rw [EReal.sub_self (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
  obtain ⟨x₀, hx₀⟩ :=
    ThetaPshAntitoneSupNondegenerate.exists_ne_bot_iInf_of_forall_exists_le htail hanti hreach
  have hinf : ThetaPlurisubharmonic θ.val (fun x => ⨅ m, tailEnvelope ŝ m x) :=
    ThetaPshDecreasingLimit.thetaPlurisubharmonic_iInf_of_antitone (fun m => (htail m).1) hanti
  refine ⟨c, hc, hcx, ⟨hinf,
    ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hinf ⟨x₀, hx₀⟩⟩, fun m => ?_⟩
  exact uscRegularization_le upperSemicontinuous_const (sSup_le fun w hw => by
    obtain ⟨j, -, rfl⟩ := hw
    exact hŝ0 j)

end TailLimit

/-! ### `lem:domination` for a big class `{γ}` (Copy-4's hypothesis), by DDNL Lemma 4.3 -/

section BigClass

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z] [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z]

open ConvexCombEnvelopeMass ThetaPshConvexCombination FirstPass.NonKahlerLocus

/-- The diagonal mass depends on the background form only through its value. -/
theorem diagonalPotentialMass_congr {θ θ' : ClosedRealOneOneForm k Z} (h : θ = θ') {u : Z → EReal}
    (hu : IsThetaPshPotential θ.val u) (hu' : IsThetaPshPotential θ'.val u) :
    diagonalPotentialMass θ u hu = diagonalPotentialMass θ' u hu' := by
  subst h
  rfl

/-- **A big class `{γ}` has a potential in `γ - δ₀ω`** for some `δ₀ > 0`: the potential of a
Kähler current `T ≥ ω_T` in `{γ}`, with `ω_T ≥ A⁻¹ω` (compactness), moved from the representative
of `T` to `γ` by the smooth `ddᶜ`-difference of the two representatives. -/
theorem exists_isThetaPshPotential_sub_smul_of_isBigClass (omegaZ : KahlerBackground k Z)
    (γ : ClosedRealOneOneForm k Z) (hbig : IsBigClass (RealBottChern.ofRepresentative γ)) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ u₀ : Z → EReal, IsThetaPshPotential (γ - δ₀ • omegaZ.form).val u₀ := by
  obtain ⟨T⟩ := hbig
  obtain ⟨A, hA, hsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul T.lowerBound (-omegaZ.form)
  have hAinv : (0 : ℝ) < A⁻¹ := inv_pos.2 hA
  have hdom : (T.lowerBound.form - A⁻¹ • omegaZ.form).val.IsSemipositive := by
    have := KahlerDomination.isSemipositive_smul hsemi hAinv.le
    have heq : A⁻¹ • (-omegaZ.form + A • T.lowerBound.form)
        = T.lowerBound.form - A⁻¹ • omegaZ.form := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt hA), one_smul, smul_neg]
      abel
    rwa [heq] at this
  have h1 : IsThetaPshPotential (T.representative - A⁻¹ • omegaZ.form).val T.potential := by
    have := LocalPotentials.isThetaPshPotential_add_of_semipositive T.strictlyPsh hdom
    rwa [sub_add_sub_cancel] at this
  have hrel : ClosedRealOneOneForm.BottChernRel (T.representative - A⁻¹ • omegaZ.form)
      (γ - A⁻¹ • omegaZ.form) := by
    have h := (RealBottChern.ofRepresentative_eq_iff _ _).mp T.represents
    simpa only [sub_eq_add_neg] using
      h.add (ClosedRealOneOneForm.BottChernRel.refl (-(A⁻¹ • omegaZ.form)))
  obtain ⟨f, hf, heq⟩ := hrel
  exact ⟨A⁻¹, hAinv, _, PositiveClasses.thetaPshPotential_sub_smooth hf heq h1⟩

/-- **A uniform bound for the masses in the classes `γ + ηω`, `η ≤ 1`**: with `γ + Aω ≥ 0` and
`B = A + 1`, every `ψ ∈ PSH(Z, γ + ηω)` has `∫(γ + ηω)_ψ^k ≤ ∫(γ + Bω)_ψ^k ≤ ∫(γ + Bω)^k < ∞`
(background monotonicity, then monotonicity against the potential `0` of the semipositive form
`γ + Bω`). -/
theorem exists_diagonalPotentialMass_le [Nonempty Z] (omegaZ : KahlerBackground k Z)
    (γ : ClosedRealOneOneForm k Z) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ η : ℝ, η ≤ 1 → ∀ (ψ : Z → EReal)
      (hψ : IsThetaPshPotential (γ + η • omegaZ.form).val ψ),
        diagonalPotentialMass (γ + η • omegaZ.form) ψ hψ ≤ M := by
  obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omegaZ γ
  have hB : (γ + (A + 1) • omegaZ.form).val.IsSemipositive := by
    have h := (LocalPotentials.thetaPlurisubharmonic_zero_iff (γ + A • omegaZ.form)).mpr hsemi
    have h' := LocalPotentials.thetaPlurisubharmonic_add_of_semipositive h omegaZ.isSemipositive
    rw [show γ + A • omegaZ.form + omegaZ.form = γ + (A + 1) • omegaZ.form by module] at h'
    exact (LocalPotentials.thetaPlurisubharmonic_zero_iff _).mp h'
  have h0 : IsThetaPshPotential (γ + (A + 1) • omegaZ.form).val (fun _ => (0 : EReal)) :=
    ⟨(LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr hB,
      fun x _ _ hx => ⟨x, hx, EReal.zero_ne_bot⟩⟩
  refine ⟨diagonalPotentialMass (γ + (A + 1) • omegaZ.form) (fun _ => 0) h0,
    GlobalNonPluripolar.globalMixedMeasure_apply_lt_top omegaZ _ univ, fun η hη ψ hψ => ?_⟩
  have hc : 0 < A + 1 - η := by linarith
  have hψ' : IsThetaPshPotential (γ + η • omegaZ.form + (A + 1 - η) • omegaZ.form).val ψ :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hψ
      (KahlerDomination.isSemipositive_smul omegaZ.isSemipositive hc.le)
  have hform : γ + η • omegaZ.form + (A + 1 - η) • omegaZ.form = γ + (A + 1) • omegaZ.form := by
    module
  have hψ'' : IsThetaPshPotential (γ + (A + 1) • omegaZ.form).val ψ := hform ▸ hψ'
  obtain ⟨C, hC⟩ := hψ.exists_global_upper_bound
  calc diagonalPotentialMass (γ + η • omegaZ.form) ψ hψ
      ≤ diagonalPotentialMass (γ + η • omegaZ.form + (A + 1 - η) • omegaZ.form) ψ hψ' :=
        AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul omegaZ.isSemipositive hc
          hψ hψ'
    _ = diagonalPotentialMass (γ + (A + 1) • omegaZ.form) ψ hψ'' :=
        diagonalPotentialMass_congr hform hψ' hψ''
    _ ≤ diagonalPotentialMass (γ + (A + 1) • omegaZ.form) (fun _ => 0) h0 :=
        diagonalPotentialMass_mono_of_kahler omegaZ hψ'' h0
          ⟨C, fun x _ => by simpa using hC x⟩

/-- A weight `a > 1` with `(a^k - 1) M < h`, for `M < ∞` and `h > 0`. -/
theorem exists_one_lt_ofReal_pow_sub_one_mul_lt {M h : ℝ≥0∞} (hM : M ≠ ⊤) (hh : 0 < h)
    (k : ℕ) : ∃ a : ℝ, 1 < a ∧ ENNReal.ofReal (a ^ k - 1) * M < h := by
  obtain ⟨ε, hε, hεh⟩ : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε ≤ h := by
    refine ⟨(min h 1).toReal, ENNReal.toReal_pos (ne_of_gt (lt_min hh one_pos))
      (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)), ?_⟩
    rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))]
    exact min_le_left _ _
  have hcont : Tendsto (fun a : ℝ => (a ^ k - 1) * M.toReal) (𝓝[>] 1) (𝓝 0) := by
    have : Tendsto (fun a : ℝ => (a ^ k - 1) * M.toReal) (𝓝 1) (𝓝 ((1 ^ k - 1) * M.toReal)) :=
      ((continuous_pow k).sub continuous_const |>.mul continuous_const).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  have h1 : ∀ᶠ a in 𝓝[>] (1 : ℝ), 1 < a := self_mem_nhdsWithin
  obtain ⟨a, ha1, hasmall⟩ := (h1.and (hcont.eventually (gt_mem_nhds hε))).exists
  refine ⟨a, ha1, lt_of_lt_of_le ?_ hεh⟩
  have hnn : 0 ≤ a ^ k - 1 := sub_nonneg.2 (one_le_pow₀ (le_of_lt ha1))
  rw [← ENNReal.ofReal_toReal hM, ← ENNReal.ofReal_mul hnn]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hasmall

/-- **Xia's interval (2.28) from a mass gap**: if `h ≤ m_φ ≤ m_ψ ≤ M < ∞` and `(a^k - 1) M < h`,
then `a` is admissible for `(m_φ, m_ψ)`:
`a^k (m_ψ - m_φ) = (m_ψ - m_φ) + (a^k - 1)(m_ψ - m_φ) < (m_ψ - m_φ) + h ≤ m_ψ`. -/
theorem isAdmissibleWeight_of_le {mφ mψ M h : ℝ≥0∞} {a : ℝ} (ha : 1 < a) (hM : M ≠ ⊤)
    (hhφ : h ≤ mφ) (hφψ : mφ ≤ mψ) (hψM : mψ ≤ M)
    (hsmall : ENNReal.ofReal (a ^ k - 1) * M < h) : IsAdmissibleWeight k mφ mψ a := by
  refine ⟨ha, ?_⟩
  have hfin : mψ - mφ ≠ ⊤ := ne_top_of_le_ne_top hM (tsub_le_self.trans hψM)
  have hak : ENNReal.ofReal (a ^ k) = 1 + ENNReal.ofReal (a ^ k - 1) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one
      (sub_nonneg.2 (one_le_pow₀ (le_of_lt ha)))]
    congr 1
    ring
  calc ENNReal.ofReal (a ^ k) * (mψ - mφ)
      = (mψ - mφ) + ENNReal.ofReal (a ^ k - 1) * (mψ - mφ) := by rw [hak, add_mul, one_mul]
    _ ≤ (mψ - mφ) + ENNReal.ofReal (a ^ k - 1) * M := by
        gcongr
        exact tsub_le_self.trans hψM
    _ < (mψ - mφ) + h := ENNReal.add_lt_add_left hfin hsmall
    _ ≤ (mψ - mφ) + mφ := by gcongr
    _ = mψ := tsub_add_cancel_of_le hφψ

/-- **Copy-4 `lem:domination`, for a big class `{γ}`** (the hypothesis under which Copy-4 states
it), by a direct argument: no log resolution, no bigness criterion, no limit.

Let `T = γ + ddᶜu₀ ≥ δ₀ω` be a Kähler current in `{γ}` and `M` the uniform mass bound of
`exists_diagonalPotentialMass_le`; choose `a > 1` with `(a^k - 1) M < h₀`.  For `η ∈ [0,1]` and
`v ∈ PSH(Z, γ_η)` with `∫(γ_η)_v^k ≥ h₀`, put `ψ := max(v, u₀) ∈ PSH(Z, γ_η)`.  Then `a` is
admissible for `v ≤ ψ` and DDNL Lemma 4.3 = Xia SGPT Lemma 2.4.4 for the big class `γ_η`
(`PositiveCurrentRooftop.exists_thetaPsh_convexCombBarrier_of_isBigClass`) gives
`w ∈ PSH(Z, γ_η)` with `a⁻¹w + (1 - a⁻¹)ψ ≤ v`.  The potential `s := a⁻¹w + (1 - a⁻¹)u₀` lies in
`PSH(Z, γ_η - (1 - a⁻¹)δ₀ω)` and `s ≤ a⁻¹w + (1 - a⁻¹)ψ ≤ v` EVERYWHERE, so `S = γ_η + ddᶜs ≥ δ_*ω`
with `δ_* = (1 - a⁻¹)δ₀`, depending only on `(Z, ω)`, `γ` and `h₀`, and `S ≼_I v`. -/
theorem dominationLemma_of_isBigClass [Nonempty Z] [ConnectedSpace Z]
    (omegaZ : KahlerBackground k Z) (γ : ClosedRealOneOneForm k Z)
    (hbig : IsBigClass (RealBottChern.ofRepresentative γ)) :
    PositiveCurrentAssembly.DominationLemma omegaZ γ := by
  intro h₀ hh₀
  obtain ⟨δ₀, hδ₀, u₀, hu₀⟩ := exists_isThetaPshPotential_sub_smul_of_isBigClass omegaZ γ hbig
  obtain ⟨M, hMtop, hM⟩ := exists_diagonalPotentialMass_le omegaZ γ
  obtain ⟨a, ha, hsmall⟩ := exists_one_lt_ofReal_pow_sub_one_mul_lt hMtop.ne hh₀ k
  have ha0 : 0 < a⁻¹ := inv_pos.2 (zero_lt_one.trans ha)
  have ha1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  refine ⟨(1 - a⁻¹) * δ₀, mul_pos (by linarith) hδ₀, ?_⟩
  intro η hη0 hη1 v hv hmass
  -- `u₀ ∈ PSH(Z, γ_η - δ₀ω) ⊆ PSH(Z, γ_η)`
  have hu₀' : IsThetaPshPotential (γ + η • omegaZ.form - δ₀ • omegaZ.form).val u₀ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hu₀
      (KahlerDomination.isSemipositive_smul omegaZ.isSemipositive hη0)
    rwa [show γ - δ₀ • omegaZ.form + η • omegaZ.form =
      γ + η • omegaZ.form - δ₀ • omegaZ.form by abel] at h
  have hu₀θ : IsThetaPshPotential (γ + η • omegaZ.form).val u₀ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hu₀'
      (KahlerDomination.isSemipositive_smul omegaZ.isSemipositive hδ₀.le)
    rwa [sub_add_cancel] at h
  have hbigθ : IsBigClass (RealBottChern.ofRepresentative (γ + η • omegaZ.form)) :=
    ⟨AmbientConvexCurrent.kahlerCurrentOfSubSmul omegaZ hδ₀ hu₀'⟩
  -- the comparison potential `ψ = max(v, u₀)`
  have hψ : IsThetaPshPotential (γ + η • omegaZ.form).val (fun x => max (v x) (u₀ x)) :=
    SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max hv hu₀θ
  have hvψ : v ≤ fun x => max (v x) (u₀ x) := fun x => le_max_left _ _
  have hmono := diagonalPotentialMass_mono_of_kahler omegaZ hv hψ
    (MoreSingularOn.of_le fun x _ => hvψ x)
  have hpos : 0 < diagonalPotentialMass (γ + η • omegaZ.form) v hv := lt_of_lt_of_le hh₀ hmass
  have hadm := isAdmissibleWeight_of_le ha hMtop.ne hmass hmono (hM η hη1 _ hψ) hsmall
  obtain ⟨w, hw, hcomb⟩ := PositiveCurrentRooftop.exists_thetaPsh_convexCombBarrier_of_isBigClass
    omegaZ (γ + η • omegaZ.form) hbigθ hv hψ hvψ hpos hadm
  refine ⟨convexComb a⁻¹ w u₀, ?_, ?_⟩
  · have hw0 : IsThetaPshPotential (γ + η • omegaZ.form - (0 : ℝ) • omegaZ.form).val w := by
      rwa [zero_smul, sub_zero]
    have h := AmbientConvexCurrent.isThetaPshPotential_convexComb_sub_smul omegaZ ha0 ha1 hw0 hu₀'
    rwa [mul_zero, zero_add] at h
  · have hle : convexComb a⁻¹ w u₀ ≤ v :=
      (convexComb_mono ha0.le ha1.le le_rfl fun x => le_max_right (v x) (u₀ x)).trans hcomb
    exact iOrderOnManifold_of_le hv.1.quasiPlurisubharmonic hle

end BigClass

end

end SGPT.Foundations.Analysis.Pending.DivisorialDomination

import SGPT.Okounkov.TranscendentalWNCone
import SGPT.Foundations.Analysis.Pending.GlobalSlotLinear
import SGPT.Foundations.Analysis.Pending.AmbientConvexCurrent
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling

/-!
# Two-sided perturbation bounds and continuity of the restricted volume

Blueprint nodes `tok-wn:restricted-mass-convex` and `tok-wn:restricted-perturbation`
(chapter `claude-tok-wn`): for a connected compact complex manifold `V` with a holomorphic map
`ι : V → X` into a compact Kähler manifold (dimension `k`, `ι^*ω` Kähler; e.g. a connected
closed submanifold `Z`), a class `ξ = {θ}` that is big with `ι(V) ⊄ E_nK(ξ)` and a closed real
smooth `(1,1)`-form `γ`, there are `A, s₀ > 0` with

`(1 - A|s|)^k R(ξ) ≤ R(ξ + s{γ})` and `(1 - A|s|)^k R(ξ + s{γ}) ≤ R(ξ)` for `|s| ≤ s₀`,

where `R = vol_{X|Z}` is the restricted volume of DRWNXZ §2. Hence `s ↦ R(ξ + s{γ})` is
continuous at `s = 0` (Matsumura 2013, Corollary 4.11; Collins--Tosatti, Corollary 5.3, for
the restricted volume of DRWNXZ). This is the continuity used by WN21 in its last step and by
DRWNXZ in the proof of Theorem 2.10.

## Proof

Let `θ + dd^c ψ ≥ κ` be a Kähler current in `ξ` with analytic singularities and polar set
`E_nK(ξ)` (Boucksom), so `ψ` is finite somewhere on `Z`, and choose `s₁ > 0` with
`κ + μγ ≥ 0` for `|μ| ≤ s₁`. The key estimate (`pow_mul_restrictedVolume_le`) is: if
`θ = (1 - λ)θ' + λβ` with `0 < λ < 1`, both classes `{θ}`, `{θ'}` big with Kähler loci meeting
`Z`, and `ψ ∈ PSH(X, β)` finite somewhere on `Z`, then `(1 - λ)^k R(θ') ≤ R(θ)`. Indeed
`u = (1 - λ)V_{θ'} + λψ ∈ PSH(X, θ)`, so `u ≤ V_θ + C`; by the identification
`R = ∫_Z ⟨(θ|_Z + dd^c V_θ|_Z)^k⟩` (`restrictedVolume_eq_restrictedMinimalMass`) and the
monotonicity of non-pluripolar masses, `R(θ) ≥ ∫_Z ⟨(θ|_Z + dd^c u|_Z)^k⟩`, and
`⟨(θ|_Z + dd^c u|_Z)^k⟩ ≥ (1 - λ)^k ⟨(θ'|_Z + dd^c V_{θ'}|_Z)^k⟩` by multilinearity
(`globalMixedMeasure_diagonal_convexComb_forms_le`, the two-form version of TN's
`globalMixedMeasure_diagonal_convexComb_le`). With `λ = |s|/s₁` it is applied to
`θ + sγ = (1 - λ)θ + λ(θ + (s/λ)γ)` and to `θ = (1 - λ)(θ + sγ) + λ(θ - ((1 - λ)s/λ)γ)`.

## Main results

* `globalMixedMeasure_diagonal_convexComb_forms_le`,
  `diagonalPotentialMass_convexComb_forms_le`: `t^N ⟨(α + dd^c a)^N⟩ ≤
  ⟨((tα + (1 - t)β) + dd^c(ta + (1 - t)b))^N⟩`;
* `pow_mul_restrictedVolume_le`: the key estimate;
* `exists_restrictedVolume_add_smul_bounds`: the two-sided bounds;
* `continuousAt_restrictedVolume_add_smul`, `continuousAt_classRestrictedVolume_add_smul`:
  continuity at `s = 0` (**`tok-wn:restricted-perturbation`**).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory
open scoped ENNReal Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

/-! ### Multilinearity: a convex combination with two forms -/

section MassConvex

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **Diagonal domination along a convex combination of two forms.** For a genuine `α`-psh
potential `a`, a genuine `β`-psh potential `b` and `0 < t < 1`,
`t^n ⟨(α + dd^c a)^n⟩(S) ≤ ⟨((tα + (1 - t)β) + dd^c(ta + (1 - t)b))^n⟩(S)` for every `S`
(multilinearity of non-pluripolar products, dropping the terms containing `β + dd^c b`).
The proof replaces one slot at a time (`GlobalSlotLinear.globalMixedMeasure_update_add_smul`),
as TN's `GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le` does for
`α = β`. -/
theorem globalMixedMeasure_diagonal_convexComb_forms_le {α β : ClosedRealOneOneForm n M}
    {a b : M → EReal} (ha : IsThetaPshPotential α.val a) (hb : IsThetaPshPotential β.val b)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (S : Set M) :
    ENNReal.ofReal (t ^ n) *
        globalMixedMeasure (fun _ => α) (fun _ => a) (fun _ => ha.1) S ≤
      globalMixedMeasure (fun _ => t • α + (1 - t) • β) (fun _ => convexComb t a b)
        (fun _ => (AmbientConvexCurrent.isThetaPshPotential_convexComb_forms ha hb ht0 ht1).1)
        S := by
  have hr : 0 < 1 - t := by linarith
  set θ : ClosedRealOneOneForm n M := t • α + (1 - t) • β with hθ_def
  set w : M → EReal := convexComb t a b with hw_def
  have hwθ : ThetaPlurisubharmonic θ.val w :=
    (AmbientConvexCurrent.isThetaPshPotential_convexComb_forms ha hb ht0 ht1).1
  -- The tuples whose first `m` slots carry `(θ, w)` and the others `(α, a)`.
  let Θ : ℕ → Fin n → ClosedRealOneOneForm n M := fun m i => if (i : ℕ) < m then θ else α
  let x : ℕ → Fin n → M → EReal := fun m i => if (i : ℕ) < m then w else a
  have hx : ∀ m i, ThetaPlurisubharmonic (Θ m i).val (x m i) := by
    intro m i
    by_cases h : (i : ℕ) < m
    · simpa only [Θ, x, h, if_true] using hwθ
    · simpa only [Θ, x, h, if_false] using ha.1
  have step : ∀ m, m ≤ n → ∀ S : Set M, ENNReal.ofReal (t ^ m) *
      globalMixedMeasure (fun _ => α) (fun _ => a) (fun _ => ha.1) S ≤
      globalMixedMeasure (Θ m) (x m) (hx m) S := by
    intro m
    induction m with
    | zero =>
      intro _ S
      have eΘ : Θ 0 = fun _ => α := by funext i; simp [Θ]
      have e : x 0 = fun _ => a := by funext i; simp [x]
      rw [pow_zero, ENNReal.ofReal_one, one_mul,
        GlobalDiagonalScaling.globalMixedMeasure_congr eΘ e (hx 0) (fun _ => ha.1)]
    | succ m ih =>
      intro hm S
      have hmn : m < n := hm
      set i₀ : Fin n := ⟨m, hmn⟩ with hi₀
      have eΘ1 : Θ (m + 1) = Function.update (Θ m) i₀ θ := by
        funext i
        by_cases h : i = i₀
        · rw [h, Function.update_self]; simp [Θ, i₀]
        · rw [Function.update_of_ne h]
          have him : (i : ℕ) ≠ m := fun h' => h (Fin.ext h')
          simp only [Θ]
          split_ifs <;> first | rfl | omega
      have e1 : x (m + 1) = Function.update (x m) i₀ w := by
        funext i
        by_cases h : i = i₀
        · rw [h, Function.update_self]; simp [x, i₀]
        · rw [Function.update_of_ne h]
          have him : (i : ℕ) ≠ m := fun h' => h (Fin.ext h')
          simp only [x]
          split_ifs <;> first | rfl | omega
      have eΘ2 : Function.update (Θ (m + 1)) i₀ α = Θ m := by
        funext i
        by_cases h : i = i₀
        · rw [h, Function.update_self]; simp [Θ, i₀]
        · rw [Function.update_of_ne h, eΘ1, Function.update_of_ne h]
      have e2 : Function.update (x m) i₀ a = x m := by
        funext i
        by_cases h : i = i₀
        · rw [h, Function.update_self]; simp [x, i₀]
        · rw [Function.update_of_ne h]
      have hc' : ∀ i, ThetaPlurisubharmonic (Θ (m + 1) i).val
          (Function.update (x m) i₀ (fun p => (t : EReal) * a p +
            ((1 - t : ℝ) : EReal) * b p) i) := by
        have : (fun p => (t : EReal) * a p + ((1 - t : ℝ) : EReal) * b p) = w := rfl
        rw [this, ← e1]; exact hx (m + 1)
      have ha' : ∀ i, ThetaPlurisubharmonic
          (Function.update (Θ (m + 1)) i₀ α i).val
          (Function.update (x m) i₀ a i) := by
        rw [eΘ2, e2]; exact hx m
      have hb' : ∀ i, ThetaPlurisubharmonic
          (Function.update (Θ (m + 1)) i₀ β i).val
          (Function.update (x m) i₀ b i) := by
        intro i
        by_cases h : i = i₀
        · rw [h, Function.update_self, Function.update_self]; exact hb.1
        · rw [Function.update_of_ne h, Function.update_of_ne h, eΘ1,
            Function.update_of_ne h]
          exact hx m i
      have hpa : globalMixedMeasure _ _ hb' {p | a p = ⊥} = 0 :=
        GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate hb' ha
      have hpb : globalMixedMeasure _ _ ha' {p | b p = ⊥} = 0 :=
        GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate ha' hb
      have hθi₀ : Θ (m + 1) i₀ = t • α + (1 - t) • β := by
        simp [Θ, i₀, hθ_def]
      have hlin := GlobalSlotLinear.globalMixedMeasure_update_add_smul
        (θ := Θ (m + 1)) i₀ ht0 hr hθi₀ hc' ha' hb' hpa hpb
      have hA : globalMixedMeasure (Function.update (Θ (m + 1)) i₀ α)
          (Function.update (x m) i₀ a) ha' = globalMixedMeasure (Θ m) (x m) (hx m) :=
        GlobalDiagonalScaling.globalMixedMeasure_congr eΘ2 e2 _ _
      have hC : globalMixedMeasure (Θ (m + 1)) (x (m + 1)) (hx (m + 1)) =
          globalMixedMeasure (Θ (m + 1))
            (Function.update (x m) i₀ (fun p => (t : EReal) * a p +
              ((1 - t : ℝ) : EReal) * b p)) hc' :=
        GlobalDiagonalScaling.globalMixedMeasure_congr rfl e1 _ _
      rw [hC, hlin, hA, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      calc ENNReal.ofReal (t ^ (m + 1)) *
            globalMixedMeasure (fun _ => α) (fun _ => a) (fun _ => ha.1) S
          = ENNReal.ofReal t * (ENNReal.ofReal (t ^ m) *
            globalMixedMeasure (fun _ => α) (fun _ => a) (fun _ => ha.1) S) := by
            rw [pow_succ', ENNReal.ofReal_mul ht0.le, mul_assoc]
        _ ≤ ENNReal.ofReal t * globalMixedMeasure (Θ m) (x m) (hx m) S := by
            gcongr
            exact ih (Nat.le_of_succ_le hm) S
        _ ≤ _ := le_self_add
  have hfullΘ : Θ n = fun _ => θ := by funext i; simp [Θ, i.isLt]
  have hfull : x n = fun _ => w := by funext i; simp [x, i.isLt]
  calc ENNReal.ofReal (t ^ n) *
        globalMixedMeasure (fun _ => α) (fun _ => a) (fun _ => ha.1) S
      ≤ globalMixedMeasure (Θ n) (x n) (hx n) S := step n le_rfl S
    _ = _ := by rw [GlobalDiagonalScaling.globalMixedMeasure_congr hfullΘ hfull (hx n) _]

/-- **`tok-wn:restricted-mass-convex`**, total masses: for a genuine `α`-psh potential `a`, a
genuine `β`-psh potential `b` and `0 < t < 1`,
`t^n ∫ ⟨(α + dd^c a)^n⟩ ≤ ∫ ⟨((tα + (1 - t)β) + dd^c(ta + (1 - t)b))^n⟩`. -/
theorem diagonalPotentialMass_convexComb_forms_le {α β : ClosedRealOneOneForm n M}
    {a b : M → EReal} (ha : IsThetaPshPotential α.val a) (hb : IsThetaPshPotential β.val b)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ENNReal.ofReal (t ^ n) * diagonalPotentialMass α a ha ≤
      diagonalPotentialMass (t • α + (1 - t) • β) (convexComb t a b)
        (AmbientConvexCurrent.isThetaPshPotential_convexComb_forms ha hb ht0 ht1) :=
  globalMixedMeasure_diagonal_convexComb_forms_le ha hb ht0 ht1 univ

omit [BorelSpace M] in
/-- The diagonal non-pluripolar mass depends only on the form and the potential. -/
theorem diagonalPotentialMass_congr {θ θ' : ClosedRealOneOneForm n M}
    {u u' : M → EReal} (h : θ = θ') (hu : u = u') (h₁ : IsThetaPshPotential θ.val u)
    (h₂ : IsThetaPshPotential θ'.val u') :
    diagonalPotentialMass θ u h₁ = diagonalPotentialMass θ' u' h₂ := by
  subst h hu
  rfl

end MassConvex

/-! ### Elementary helpers -/

section Helpers

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A Kähler current `θ_T + dd^c φ ≥ κ` in the class of `θ` gives the `(θ - κ)`-psh potential
`φ - f` (`θ = θ_T + dd^c f`), with the same poles as `φ`. -/
theorem exists_isThetaPshPotential_sub_lowerBound {θ : ClosedRealOneOneForm n M}
    (K : KahlerCurrent (RealBottChern.ofRepresentative θ)) :
    ∃ ψ : M → EReal, IsThetaPshPotential (θ - K.lowerBound.form).val ψ ∧
      ∀ x, ψ x = ⊥ ↔ K.potential x = ⊥ := by
  obtain ⟨f, hf, hfeq⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp K.represents
  refine ⟨fun x => K.potential x - (f x : EReal), ?_, fun x => ?_⟩
  · refine PositiveClasses.thetaPshPotential_sub_smooth hf ?_ K.strictlyPsh
    intro e z hz
    simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
      hfeq e z hz]
    abel
  · constructor
    · intro hbot
      change K.potential x - (f x : EReal) = ⊥ at hbot
      rw [sub_eq_add_neg, EReal.add_eq_bot_iff] at hbot
      rcases hbot with h | h
      · exact h
      · rw [← EReal.coe_neg] at h
        exact absurd h (EReal.coe_ne_bot _)
    · intro h
      simp only [h, EReal.bot_sub]

/-- A big class `{θ}` has a genuine `θ`-psh potential. -/
theorem exists_isThetaPshPotential_of_isBigClass {θ : ClosedRealOneOneForm n M}
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ u : M → EReal, IsThetaPshPotential θ.val u := by
  obtain ⟨K⟩ := hbig
  obtain ⟨ψ, hψ, -⟩ := exists_isThetaPshPotential_sub_lowerBound K
  refine ⟨ψ, ?_⟩
  have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hψ
    K.lowerBound.isSemipositive
  rwa [sub_add_cancel] at h

/-- If `ψ ∈ PSH(X, θ - κ)` and `κ/2 + μγ ≥ 0`, then `ψ ∈ PSH(X, θ + μγ)`. -/
theorem isThetaPshPotential_add_smul_of_sub_lowerBound {θ γ : ClosedRealOneOneForm n M}
    (κ : KahlerBackground n M) {ψ : M → EReal} (hψ : IsThetaPshPotential (θ - κ.form).val ψ)
    {μ : ℝ} (hμ : (((1 / 2 : ℝ)) • κ.form + μ • γ).val.IsSemipositive) :
    IsThetaPshPotential (θ + μ • γ).val ψ := by
  have h1 := LocalPotentials.isThetaPshPotential_add_of_semipositive hψ hμ
  have h2 := LocalPotentials.isThetaPshPotential_add_of_semipositive h1
    (KahlerDomination.isSemipositive_smul κ.isSemipositive (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have he : θ - κ.form + ((1 / 2 : ℝ) • κ.form + μ • γ) + (1 / 2 : ℝ) • κ.form = θ + μ • γ := by
    module
  rwa [he] at h2

end Helpers

section Pullback

variable {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  {ι : V → X} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)

include hι in
/-- The pullback of closed real `(1,1)`-forms is additive. -/
theorem closedPullback_add (a b : ClosedRealOneOneForm n X) :
    ClosedRealOneOneForm.pullback hι (a + b) =
      ClosedRealOneOneForm.pullback hι a + ClosedRealOneOneForm.pullback hι b := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

include hι in
/-- The pullback of closed real `(1,1)`-forms is homogeneous. -/
theorem closedPullback_smul (c : ℝ) (a : ClosedRealOneOneForm n X) :
    ClosedRealOneOneForm.pullback hι (c • a) = c • ClosedRealOneOneForm.pullback hι a := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

end Pullback

/-! ### The two-sided perturbation bounds -/

section Perturbation

open TranscendentalVolumeConcavity

variable {m k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [Nonempty X]
  {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
  {ι : V → X} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel (m + 1)) ∞ ι)

omit [Nonempty X] [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V]
  [ConnectedSpace V] in
/-- **Boucksom's current, restricted.** If `{θ}` is big and `ι(V)` meets its Kähler locus,
there are a Kähler form `κ` and `ψ ∈ PSH(X, θ - κ)` (a Kähler current with analytic
singularities and polar set `E_nK`) which is finite somewhere on `ι(V)`. -/
theorem exists_kahler_potential_finite_on (θ : ClosedRealOneOneForm (m + 1) X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hZ : ∃ y : V, ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ)) :
    ∃ κ : KahlerBackground (m + 1) X, ∃ ψ : X → EReal,
      IsThetaPshPotential (θ - κ.form).val ψ ∧ ∃ y : V, ψ (ι y) ≠ ⊥ := by
  obtain ⟨y₀, hy₀⟩ := hZ
  obtain ⟨K, -, hKpole⟩ :=
    NonKahlerLocusPoleSetBounded.exists_kahlerCurrent_analyticSingularityType_poleSet_eq_nonKahlerLocus
      (Nat.succ_pos m) (RealBottChern.ofRepresentative θ) hbig
  obtain ⟨ψ, hψ, hpole⟩ := exists_isThetaPshPotential_sub_lowerBound K
  refine ⟨K.lowerBound, ψ, hψ, y₀, fun hbot => hy₀ ?_⟩
  rw [← hKpole]
  exact (hpole _).mp hbot

include hι in
/-- **The key estimate** (`tok-wn:restricted-perturbation`, first step). Let
`θ = tθ' + (1 - t)β` with `0 < t < 1`, both classes `{θ}`, `{θ'}` big with Kähler loci meeting
`ι(V)`, and `ψ ∈ PSH(X, β)` finite somewhere on `ι(V)`. Then `t^k R(θ') ≤ R(θ)`.

Proof: `u = tV_{θ'} + (1 - t)ψ ∈ PSH(X, θ)`, so `u ≤ V_θ + C`, and on `V`,
`R(θ) = ∫ ⟨(θ|_V + dd^c V_θ|_V)^k⟩ ≥ ∫ ⟨(θ|_V + dd^c u|_V)^k⟩
  ≥ t^k ∫ ⟨(θ'|_V + dd^c V_{θ'}|_V)^k⟩ = t^k R(θ')`. -/
theorem pow_mul_restrictedVolume_le (w : KahlerBackground (m + 1) X)
    (hpull : (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)
    {θ θ' β : ClosedRealOneOneForm (m + 1) X} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hθ : θ = t • θ' + (1 - t) • β)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hZ : ∃ y : V, ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ))
    (hbig' : IsBigClass (RealBottChern.ofRepresentative θ'))
    (hZ' : ∃ y : V, ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ'))
    {ψ : X → EReal} (hψ : IsThetaPshPotential β.val ψ) (hψZ : ∃ y : V, ψ (ι y) ≠ ⊥) :
    ENNReal.ofReal (t ^ k) * restrictedVolume ι hι θ' ≤ restrictedVolume ι hι θ := by
  obtain ⟨hV', hR'⟩ := restrictedVolume_eq_restrictedMinimalMass hι w hpull θ' hbig' hZ'
  obtain ⟨hV, hR⟩ := restrictedVolume_eq_restrictedMinimalMass hι w hpull θ hbig hZ
  obtain ⟨u₀, hu₀⟩ := exists_isThetaPshPotential_of_isBigClass hbig'
  have hV'X : IsThetaPshPotential θ'.val (thetaPshSupremum θ'.val) :=
    FirstPass.thetaPshSupremum_isThetaPshPotential θ'.val θ'.2.1 θ'.2.2
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ') ⟨u₀, hu₀⟩
  set u : X → EReal := convexComb t (thetaPshSupremum θ'.val) ψ with hu_def
  have hu : IsThetaPshPotential θ.val u := by
    rw [hθ]
    exact AmbientConvexCurrent.isThetaPshPotential_convexComb_forms hV'X hψ ht0 ht1
  have hψι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι β).val
      (fun y => ψ (ι y)) :=
    ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hψ.1,
      ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot
        (GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hψ.1) hψZ⟩
  have hcomb := AmbientConvexCurrent.isThetaPshPotential_convexComb_forms hV' hψι ht0 ht1
  have hpullθ : ClosedRealOneOneForm.pullback hι θ =
      t • ClosedRealOneOneForm.pullback hι θ' + (1 - t) • ClosedRealOneOneForm.pullback hι β := by
    rw [hθ, closedPullback_add, closedPullback_smul, closedPullback_smul]
  have huι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
      (fun y => u (ι y)) := by
    rw [hpullθ]
    exact hcomb
  have hmass := diagonalPotentialMass_convexComb_forms_le hV' hψι ht0 ht1
  have heq := diagonalPotentialMass_congr hpullθ.symm rfl hcomb huι
  obtain ⟨C, hC⟩ := FirstPass.thetaPshSupremum_minimalSingularities θ.val θ.2.1 θ.2.2
    (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) ⟨u, hu⟩ u hu
  let ωV : KahlerBackground k V := ⟨ClosedRealOneOneForm.pullback hι w.form, hpull⟩
  have hmono := diagonalPotentialMass_mono_of_kahler ωV huι hV
    ⟨C, fun y _ => hC (ι y) (mem_univ _)⟩
  rw [hR', hR]
  calc ENNReal.ofReal (t ^ k) * diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ')
        (fun y => thetaPshSupremum θ'.val (ι y)) hV'
      ≤ _ := hmass
    _ = _ := heq
    _ ≤ _ := hmono

include hι in
/-- **`tok-wn:restricted-perturbation`, the two-sided bounds.** Let `{θ}` be big with Kähler
locus meeting `ι(V)` and `η` a closed real smooth `(1,1)`-form. There are `A > 0` and `s₀ > 0`
with `s₀ A ≤ 1/2` such that for `|s| ≤ s₀`
`(1 - A|s|)^k R(θ) ≤ R(θ + sη)` and `(1 - A|s|)^k R(θ + sη) ≤ R(θ)`. -/
theorem exists_restrictedVolume_add_smul_bounds (w : KahlerBackground (m + 1) X)
    (hpull : (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)
    (θ η : ClosedRealOneOneForm (m + 1) X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hZ : ∃ y : V, ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ)) :
    ∃ A : ℝ, 0 < A ∧ ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ * A ≤ 1 / 2 ∧ ∀ s : ℝ, |s| ≤ s₀ →
      ENNReal.ofReal ((1 - A * |s|) ^ k) * restrictedVolume ι hι θ ≤
          restrictedVolume ι hι (θ + s • η) ∧
        ENNReal.ofReal ((1 - A * |s|) ^ k) * restrictedVolume ι hι (θ + s • η) ≤
          restrictedVolume ι hι θ := by
  obtain ⟨κ, ψ, hψ, hψZ⟩ := exists_kahler_potential_finite_on θ hbig hZ
  obtain ⟨s₁, hs₁, hsemi⟩ := exists_pos_isSemipositive_half_add_smul κ η
  have hψμ : ∀ μ : ℝ, |μ| ≤ s₁ → IsThetaPshPotential (θ + μ • η).val ψ := fun μ hμ =>
    isThetaPshPotential_add_smul_of_sub_lowerBound κ hψ (hsemi μ hμ)
  obtain ⟨y₀, hy₀⟩ := hZ
  obtain ⟨s₂, hs₂, hopen⟩ := exists_isBigClass_add_smul_meeting
    (Z := range ι) ⟨ι y₀, ⟨y₀, rfl⟩, hy₀⟩ η
  have hcls : ∀ s : ℝ, RealBottChern.ofRepresentative (θ + s • η) =
      RealBottChern.ofRepresentative θ + s • RealBottChern.ofRepresentative η := fun s => rfl
  have hA : ∀ s : ℝ, |s| ≤ s₂ → IsBigClass (RealBottChern.ofRepresentative (θ + s • η)) ∧
      ∃ y : V, ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative (θ + s • η)) := by
    intro s hs
    obtain ⟨h1, y, ⟨v, rfl⟩, hv⟩ := hopen s hs
    exact ⟨by rw [hcls]; exact h1, v, by rw [hcls]; exact hv⟩
  refine ⟨1 / s₁, by positivity, min s₂ (s₁ / 2), lt_min hs₂ (by positivity), ?_, ?_⟩
  · calc min s₂ (s₁ / 2) * (1 / s₁) ≤ s₁ / 2 * (1 / s₁) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = 1 / 2 := by field_simp
  intro s hs
  have hs2 : |s| ≤ s₂ := hs.trans (min_le_left _ _)
  have hs1 : |s| ≤ s₁ / 2 := hs.trans (min_le_right _ _)
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  set lam : ℝ := 1 / s₁ * |s| with hlam
  have habs : 0 < |s| := abs_pos.mpr hs0
  have hlam0 : 0 < lam := by positivity
  have hlam1 : lam ≤ 1 / 2 := by
    calc lam = |s| / s₁ := by rw [hlam]; ring
      _ ≤ (s₁ / 2) / s₁ := by gcongr
      _ = 1 / 2 := by field_simp
  have ht0 : 0 < 1 - lam := by linarith
  have ht1 : 1 - lam < 1 := by linarith
  set μ : ℝ := s / lam with hμ
  have hsμ : s = lam * μ := by rw [hμ]; field_simp
  have habsμ : |μ| = s₁ := by
    rw [hμ, abs_div, abs_of_pos hlam0, hlam]
    field_simp
  obtain ⟨hbig_s, hZ_s⟩ := hA s hs2
  constructor
  · -- `θ + sη = (1 - λ)θ + λ(θ + μη)`
    have hform : θ + s • η = (1 - lam) • θ + (1 - (1 - lam)) • (θ + μ • η) := by
      rw [hsμ]
      module
    exact pow_mul_restrictedVolume_le hι w hpull ht0 ht1 hform hbig_s hZ_s hbig ⟨y₀, hy₀⟩
      (hψμ μ habsμ.le) hψZ
  · -- `θ = (1 - λ)(θ + sη) + λ(θ - (1 - λ)μη)`
    have hform : θ = (1 - lam) • (θ + s • η) + (1 - (1 - lam)) • (θ + (-(1 - lam) * μ) • η) := by
      rw [hsμ]
      module
    have hμ' : |(-(1 - lam) * μ)| ≤ s₁ := by
      rw [abs_mul, abs_neg, abs_of_pos ht0, habsμ]
      nlinarith
    exact pow_mul_restrictedVolume_le hι w hpull ht0 ht1 hform hbig ⟨y₀, hy₀⟩ hbig_s hZ_s
      (hψμ _ hμ') hψZ

include hι in
/-- **`tok-wn:restricted-perturbation`, continuity** (Matsumura 2013, Corollary 4.11, for the
DRWNXZ restricted volume): if `{θ}` is big with Kähler locus meeting `ι(V)` and `η` is a
closed real smooth `(1,1)`-form, then `s ↦ R(θ + sη)` is continuous at `s = 0`. -/
theorem continuousAt_restrictedVolume_add_smul (w : KahlerBackground (m + 1) X)
    (hpull : (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)
    (θ η : ClosedRealOneOneForm (m + 1) X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hZ : ∃ y : V, ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ)) :
    ContinuousAt (fun s : ℝ => (restrictedVolume ι hι (θ + s • η)).toReal) 0 := by
  obtain ⟨A, hA, s₀, hs₀, hs₀A, hbd⟩ :=
    exists_restrictedVolume_add_smul_bounds hι w hpull θ η hbig hZ
  let ωV : KahlerBackground k V := ⟨ClosedRealOneOneForm.pullback hι w.form, hpull⟩
  have hfin : ∀ θ' : ClosedRealOneOneForm (m + 1) X, restrictedVolume ι hι θ' ≠ ⊤ :=
    fun θ' => (restrictedVolume_lt_top hι ωV θ').ne
  set r₀ : ℝ := (restrictedVolume ι hι θ).toReal with hr₀
  set c : ℝ → ℝ := fun s => (1 - A * |s|) ^ k with hc
  have hcpos : ∀ s : ℝ, |s| ≤ s₀ → 0 < c s := by
    intro s hs
    have : A * |s| ≤ 1 / 2 := by nlinarith [abs_nonneg s]
    exact pow_pos (by linarith) k
  have hlow : ∀ s : ℝ, |s| ≤ s₀ → c s * r₀ ≤ (restrictedVolume ι hι (θ + s • η)).toReal := by
    intro s hs
    have h := ENNReal.toReal_mono (hfin _) (hbd s hs).1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hcpos s hs).le] at h
  have hupp : ∀ s : ℝ, |s| ≤ s₀ → (restrictedVolume ι hι (θ + s • η)).toReal ≤ r₀ / c s := by
    intro s hs
    have h := ENNReal.toReal_mono (hfin _) (hbd s hs).2
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hcpos s hs).le] at h
    rw [le_div_iff₀ (hcpos s hs)]
    linarith
  have hcont : Continuous c := by
    simp only [hc]
    fun_prop
  have hc0 : c 0 = 1 := by simp [hc]
  have hct : Tendsto c (𝓝 0) (𝓝 1) := by
    rw [← hc0]
    exact hcont.tendsto 0
  have hnhds : ∀ᶠ s in 𝓝 (0 : ℝ), |s| ≤ s₀ := by
    filter_upwards [Icc_mem_nhds (neg_lt_zero.mpr hs₀) hs₀] with s hs
    exact abs_le.mpr hs
  have hval : (restrictedVolume ι hι (θ + (0 : ℝ) • η)).toReal = r₀ := by
    simp [hr₀]
  rw [ContinuousAt, hval]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_
    (hnhds.mono fun s hs => hlow s hs) (hnhds.mono fun s hs => hupp s hs)
  · simpa using hct.mul_const r₀
  · have h := (tendsto_const_nhds (x := r₀)).div hct one_ne_zero
    rw [div_one] at h
    exact h

include hι in
/-- **`tok-wn:restricted-perturbation`**, class version: if `ξ` is big with Kähler locus meeting
`ι(V)` and `γ` is a closed real smooth `(1,1)`-form, then `s ↦ vol_{X|Z}(ξ + s{γ})` is
continuous at `s = 0`. -/
theorem continuousAt_classRestrictedVolume_add_smul (w : KahlerBackground (m + 1) X)
    (hpull : (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)
    (ξ : RealBottChern (m + 1) X) (γ : ClosedRealOneOneForm (m + 1) X)
    (hbig : IsBigClass ξ) (hZ : ∃ y : V, ι y ∉ nonKahlerLocus ξ) :
    ContinuousAt (fun s : ℝ => (classRestrictedVolume ι hι
      (ξ + s • RealBottChern.ofRepresentative γ)).toReal) 0 := by
  have hξ : RealBottChern.ofRepresentative (Quotient.out ξ) = ξ := Quotient.out_eq ξ
  have hfun : (fun s : ℝ => (classRestrictedVolume ι hι
      (ξ + s • RealBottChern.ofRepresentative γ)).toReal) =
      fun s : ℝ => (restrictedVolume ι hι (Quotient.out ξ + s • γ)).toReal := by
    funext s
    rw [restrictedVolume_eq_classRestrictedVolume hι]
    congr 2
    rw [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul, hξ]
  rw [hfun]
  exact continuousAt_restrictedVolume_add_smul hι w hpull (Quotient.out ξ) γ
    (by rw [hξ]; exact hbig) (by rw [hξ]; exact hZ)

end Perturbation

end SGPT.Okounkov.TranscendentalWN

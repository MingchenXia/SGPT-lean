import SGPT.Trace.TraceMass
import SGPT.Okounkov.SourceTraceChoices
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantMass
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityOrderedMassCriterion
import SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground
import SGPT.Foundations.Analysis.Pending.POrderAffineRooftop
import SGPT.Foundations.Analysis.Pending.PositiveCurrentAssembly
import SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence
import SGPT.Foundations.Analysis.Pending.AdmissibleTraceBackgroundMargin

/-!
# Restrictions to a single member: the per-member lemmas of package D

Source: `chapter_trace.tex`, Section "Analytic Bertini theorems", the proofs of
`lma:posmasscurrres`, `prop:varphiP_rest_gen`, `lma:Igoodrest` and
`cor:rest_gen_very_good` (blueprint `claude-bertini:posmasscurrres` ff.,
`claude-bertini-d:*`). Each of these proofs works on one connected smooth member `H` at a
time, after the general position conditions "`ψ|_H ≢ -∞`" for countably many quasi-psh
functions `ψ` built on `X` have been imposed. This file proves these single-member steps for
an abstract target: a compact connected complex manifold `V` of dimension `k` with a
holomorphic map `ι : V → X` whose pullback of the ambient Kähler form is Kähler (for
instance a connected closed submanifold, `ι = Subtype.val`). Restrictions are compositions
`φ ∘ ι` and `θ|_V` is the pullback `ι^*θ`.

The proofs replace the `L¹`-compactness of normalized envelopes used in the book by the
elementary mass inequality `t^k ∫ θ_b^k ≤ ∫ θ_{t b + (1-t) e}^k`
(`GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le`) and the
characterization of `d_S`-convergence of ordered sequences by convergence of masses
(`cor:decnetdS`).

Main results:

* `hasPositivePotentialMass_comp_of_le`: if `ψ ≤ φ` and `θ_ψ ≥ δω` (a Kähler current) and
  `ψ ∘ ι ≢ -∞`, then `φ ∘ ι ∈ PSH(V, ι^*θ)_{>0}` (proof of `lma:posmasscurrres`);
* `exists_barriers_of_tendsto` and `tendstoSingularityType_comp_of_barriers`: the two halves
  of the proof of `lma:Igoodrest` (ambient barriers from `lma:pathoenvelope`, then the
  convergence on `V`);
* `exists_envelope_barriers` and `sourcePOrder_comp_of_barriers`: the two halves of the
  proof of `prop:varphiP_rest_gen`;
* `isSourceTraceRepresentativeAlong_comp_of_tendsto`: a restriction which is the `d_S`-limit
  of the restricted quasi-equisingular approximation is a trace operator (`def:traceop`);
* `isSourceTraceRepresentativeAlong_of_sourcePEquivalent`: trace operators are closed under
  `P`-equivalence (they are defined only up to `d_S`-distance zero).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Trace.BertiniGeneral

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
  SGPT.Foundations.Analysis.FirstPass.TraceBackground
  SGPT.Foundations.Analysis.FirstPass.POrder
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
  SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
  SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
  SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
  SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
  SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
  SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy

/-! ### Elementary facts -/

section Elementary

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The two ways of writing a convex combination. -/
theorem convexComb_swap (t : ℝ) (u v : M → EReal) :
    convexComb t u v = convexComb (1 - t) v u := by
  funext x
  simp only [convexComb_apply, sub_sub_cancel]
  exact add_comm _ _

/-- The sum of two semipositive closed forms is semipositive. -/
theorem isSemipositive_add {a b : ClosedRealOneOneForm n M} (ha : a.val.IsSemipositive)
    (hb : b.val.IsSemipositive) : (a + b).val.IsSemipositive := by
  intro e z hz v
  exact add_nonneg (ha e z hz v) (hb e z hz v)

/-- A potential of a smaller background is a potential of a larger one. -/
theorem isThetaPshPotential_of_sub_isSemipositive {a b : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu : IsThetaPshPotential a.val u) (hab : (b - a).val.IsSemipositive) :
    IsThetaPshPotential b.val u := by
  have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hu hab
  rwa [add_sub_cancel] at h

/-- The weights `t_m = 1 - (m + 2)⁻¹ ∈ [1/2, 1)`. -/
theorem weight_pos (m : ℕ) : 0 < 1 - ((m : ℝ) + 2)⁻¹ := by
  have h : ((m : ℝ) + 2)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith)
  linarith

theorem weight_lt_one (m : ℕ) : 1 - ((m : ℝ) + 2)⁻¹ < 1 := by
  have h : 0 < ((m : ℝ) + 2)⁻¹ := by positivity
  linarith

/-- `t_m^k → 1`. -/
theorem tendsto_weight_pow (k : ℕ) :
    Tendsto (fun m : ℕ => ENNReal.ofReal ((1 - ((m : ℝ) + 2)⁻¹) ^ k)) atTop (𝓝 1) := by
  have h2 : Tendsto (fun m : ℕ => (m : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun m : ℕ => ((m : ℝ) + 2)⁻¹) atTop (𝓝 0) := h2.inv_tendsto_atTop
  have hpow : Tendsto (fun m : ℕ => (1 - ((m : ℝ) + 2)⁻¹) ^ k) atTop (𝓝 ((1 - 0) ^ k)) :=
    (tendsto_const_nhds.sub hinv).pow k
  have h := (ENNReal.continuous_ofReal.tendsto _).comp hpow
  simpa only [sub_zero, one_pow, ENNReal.ofReal_one, Function.comp_def] using h

/-- If `t_m^k b ≤ a` for every `m`, then `b ≤ a`. -/
theorem le_of_forall_weight_mul_le {a b : ℝ≥0∞} (k : ℕ)
    (h : ∀ m : ℕ, ENNReal.ofReal ((1 - ((m : ℝ) + 2)⁻¹) ^ k) * b ≤ a) : b ≤ a := by
  have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal ((1 - ((m : ℝ) + 2)⁻¹) ^ k) * b) atTop
      (𝓝 (1 * b)) :=
    ENNReal.Tendsto.mul_const (tendsto_weight_pow k) (Or.inl one_ne_zero)
  rw [one_mul] at hlim
  exact le_of_tendsto' hlim h

end Elementary

/-! ### Masses on a compact manifold -/

section Mass

variable {k : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V]

/-- `t^k ∫ θ_b^k ≤ ∫ θ_a^k` whenever `t b + (1 - t) e ≤ a` (multilinearity of the
non-pluripolar product and monotonicity, `thm:mono`). -/
theorem mass_le_of_convexComb_le (omegaV : KahlerBackground k V)
    {η : ClosedRealOneOneForm k V} {a b e : V → EReal}
    (ha : IsThetaPshPotential η.val a) (hb : IsThetaPshPotential η.val b)
    (he : IsThetaPshPotential η.val e) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hle : convexComb t b e ≤ a) :
    ENNReal.ofReal (t ^ k) * diagonalPotentialMass η b hb ≤ diagonalPotentialMass η a ha := by
  have h1 := GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le hb he ht0 ht1
    univ
  have hc := isThetaPshPotential_convexComb hb he ht0 ht1
  have h2 := diagonalPotentialMass_mono_of_kahler omegaV hc ha
    (MoreSingularOn.of_le fun x _ => hle x)
  exact h1.trans h2

/-- **Equal masses from convex barriers.** If `a` is more singular than `b` and for every
`m` some `e_m` satisfies `t_m b + (1 - t_m) e_m ≤ a`, then `∫θ_a^k = ∫θ_b^k`. -/
theorem mass_eq_of_barriers (omegaV : KahlerBackground k V) {η : ClosedRealOneOneForm k V}
    {a b : V → EReal} (ha : IsThetaPshPotential η.val a) (hb : IsThetaPshPotential η.val b)
    (hab : MoreSingularOn a b univ)
    (hbar : ∀ m : ℕ, ∃ e : V → EReal, IsThetaPshPotential η.val e ∧
      convexComb (1 - ((m : ℝ) + 2)⁻¹) b e ≤ a) :
    diagonalPotentialMass η a ha = diagonalPotentialMass η b hb := by
  refine le_antisymm (diagonalPotentialMass_mono_of_kahler omegaV ha hb hab)
    (le_of_forall_weight_mul_le k fun m => ?_)
  obtain ⟨e, he, hle⟩ := hbar m
  exact mass_le_of_convexComb_le omegaV ha hb he (weight_pos m) (weight_lt_one m) hle

/-- **Convergence of masses from convex barriers.** Let `a ≤ b_j`, `(b_j)` decreasing, and
suppose that for every `m` there are `j` and `e_m` with `t_m b_j + (1 - t_m) e_m ≤ a`. Then
`∫θ_{b_j}^k → ∫θ_a^k`. -/
theorem tendsto_mass_of_barriers (omegaV : KahlerBackground k V)
    {η : ClosedRealOneOneForm k V} {a : V → EReal} {b : ℕ → V → EReal}
    (ha : IsThetaPshPotential η.val a) (hb : ∀ j, IsThetaPshPotential η.val (b j))
    (hab : ∀ j, a ≤ b j) (hanti : ∀ y, Antitone fun j => b j y)
    (hbar : ∀ m : ℕ, ∃ j, ∃ e : V → EReal, IsThetaPshPotential η.val e ∧
      convexComb (1 - ((m : ℝ) + 2)⁻¹) (b j) e ≤ a) :
    Tendsto (fun j => diagonalPotentialMass η (b j) (hb j)) atTop
      (𝓝 (diagonalPotentialMass η a ha)) := by
  have hmono : Antitone fun j => diagonalPotentialMass η (b j) (hb j) := fun i j hij =>
    diagonalPotentialMass_mono_of_kahler omegaV (hb j) (hb i)
      (MoreSingularOn.of_le fun y _ => hanti y hij)
  have hlim := tendsto_atTop_iInf hmono
  have heq : (⨅ j, diagonalPotentialMass η (b j) (hb j)) = diagonalPotentialMass η a ha := by
    refine le_antisymm (le_of_forall_weight_mul_le k fun m => ?_)
      (le_iInf fun j => diagonalPotentialMass_mono_of_kahler omegaV ha (hb j)
        (MoreSingularOn.of_le fun y _ => hab j y))
    obtain ⟨j, e, he, hle⟩ := hbar m
    refine le_trans ?_
      (mass_le_of_convexComb_le omegaV ha (hb j) he (weight_pos m) (weight_lt_one m) hle)
    gcongr
    exact iInf_le _ j
  rwa [heq] at hlim

end Mass

/-! ### `d_S`-convergence on the target -/

section Convergence

variable {k : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V]
  [ConnectedSpace V]

/-- `u_j → v` in `d_S` on `V`, in the sense of `cor:dSconv_changetheta` and the footnote of
`def:traceop`: for EVERY closed real `(1,1)`-form `η` on `V` representing a big class with
all `u_j, v ∈ PSH(V, η)`, `d_{S,η}(u_j, v) → 0`. (The Kähler background `omegaV` only enters
the construction of the pseudometric; the distance does not depend on it.) -/
def TendstoSingularityType (omegaV : KahlerBackground k V) (u : ℕ → V → EReal)
    (v : V → EReal) : Prop :=
  ∀ (η : ClosedRealOneOneForm k V) (hη : IsBigClass (RealBottChern.ofRepresentative η))
    (hu : ∀ j, IsThetaPshPotential η.val (u j)) (hv : IsThetaPshPotential η.val v),
    Tendsto (fun j => (⟨u j, hu j⟩ : ThetaPshL1 η.val)) atTop
      (@nhds (ThetaPshL1 η.val)
        (singularityPseudoMetricSpace omegaV η hη).toUniformSpace.toTopologicalSpace ⟨v, hv⟩)

/-- `d_S`-convergence in one big background gives it in every big background
(`cor:dSconv_changetheta`). -/
theorem tendstoSingularityType_of_tendsto (omegaV : KahlerBackground k V)
    {σ : ClosedRealOneOneForm k V} (hσ : IsBigClass (RealBottChern.ofRepresentative σ))
    {u : ℕ → V → EReal} {v : V → EReal} (hu : ∀ j, IsThetaPshPotential σ.val (u j))
    (hv : IsThetaPshPotential σ.val v)
    (hlim : Tendsto (fun j => (⟨u j, hu j⟩ : ThetaPshL1 σ.val)) atTop
      (@nhds (ThetaPshL1 σ.val)
        (singularityPseudoMetricSpace omegaV σ hσ).toUniformSpace.toTopologicalSpace ⟨v, hv⟩)) :
    TendstoSingularityType omegaV u v := fun η hη huη hvη =>
  (SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds omegaV σ η hσ hη atTop
    hu hv huη hvη).mp hlim

end Convergence

/-! ### The target -/

section Target

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)

/-- Pullback commutes with `a + t c`. -/
theorem pullback_add (a c : ClosedRealOneOneForm n M) :
    ClosedRealOneOneForm.pullback hι (a + c) =
      ClosedRealOneOneForm.pullback hι a + ClosedRealOneOneForm.pullback hι c := by
  have h := NefCoreKahlerCurrent.pullback_add_smul hι a c 1
  rwa [one_smul, one_smul] at h

/-- Pullback commutes with `a - t c`. -/
theorem pullback_sub_smul (a c : ClosedRealOneOneForm n M) (t : ℝ) :
    ClosedRealOneOneForm.pullback hι (a - t • c) =
      ClosedRealOneOneForm.pullback hι a - t • ClosedRealOneOneForm.pullback hι c := by
  have h1 : a - t • c = a + (-t) • c := by module
  rw [h1, NefCoreKahlerCurrent.pullback_add_smul]
  module

/-- Restriction of a potential not identically `-∞` on the (connected) target: `φ|_V ∈
PSH(V, θ|_V)` (`φ|_V ≢ -∞` is the book's well-definedness condition). -/
theorem isThetaPshPotential_comp [ConnectedSpace V] {θ : ClosedRealOneOneForm n M}
    {φ : M → EReal} (hφ : IsThetaPshPotential θ.val φ) (hne : ∃ y, φ (ι y) ≠ ⊥) :
    IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val (fun y => φ (ι y)) :=
  ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hφ.1,
    ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot
      (GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hφ.1) hne⟩

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V] in
/-- A function above one which is not identically `-∞` on `V` is not identically `-∞`. -/
theorem exists_ne_bot_of_le {φ ψ : M → EReal} (hle : φ ≤ ψ) (h : ∃ y, φ (ι y) ≠ ⊥) :
    ∃ y, ψ (ι y) ≠ ⊥ := by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, fun h0 => hy (le_bot_iff.mp (h0 ▸ hle (ι y)))⟩

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V] in
/-- The same for an additive comparison `φ ≤ ψ + C`. -/
theorem exists_ne_bot_of_moreSingularOn {φ ψ : M → EReal} (hle : MoreSingularOn φ ψ univ)
    (h : ∃ y, φ (ι y) ≠ ⊥) : ∃ y, ψ (ι y) ≠ ⊥ := by
  obtain ⟨C, hC⟩ := hle
  obtain ⟨y, hy⟩ := h
  refine ⟨y, fun h0 => hy (le_bot_iff.mp ?_)⟩
  have := hC (ι y) (mem_univ _)
  rwa [h0, EReal.bot_add] at this

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V] in
/-- Additive comparisons restrict. -/
theorem moreSingularOn_comp {φ ψ : M → EReal} (hle : MoreSingularOn φ ψ univ) :
    MoreSingularOn (fun y => φ (ι y)) (fun y => ψ (ι y)) univ := by
  obtain ⟨C, hC⟩ := hle
  exact ⟨C, fun y _ => hC (ι y) (mem_univ _)⟩

/-- The pulled-back Kähler background. -/
def pullbackKahler (omega : KahlerBackground n M)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler) : KahlerBackground k V :=
  ⟨ClosedRealOneOneForm.pullback hι omega.form, hpull⟩

/-- On the target, `ι^*(θ + 1 • ω) = ι^*θ + 1 • ι^*ω`. -/
theorem pullback_add_kahler (omega : KahlerBackground n M)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M) :
    ClosedRealOneOneForm.pullback hι (θ + (1 : ℝ) • omega.form) =
      ClosedRealOneOneForm.pullback hι θ + (1 : ℝ) • (pullbackKahler hι omega hpull).form :=
  NefCoreKahlerCurrent.pullback_add_smul hι θ omega.form 1

variable [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- A restricted `θ|_V`-potential is a potential of `θ|_V + ω|_V` with positive mass, and this
class is big. -/
theorem positive_of_add_kahler (omega : KahlerBackground n M)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    {θ : ClosedRealOneOneForm n M} {u : V → EReal}
    (hu : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val u) :
    IsBigClass (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hι θ + (1 : ℝ) • (pullbackKahler hι omega hpull).form)) ∧
      ∃ hu' : IsThetaPshPotential
          (ClosedRealOneOneForm.pullback hι θ + (1 : ℝ) • (pullbackKahler hι omega hpull).form).val u,
        HasPositivePotentialMass
          (ClosedRealOneOneForm.pullback hι θ + (1 : ℝ) • (pullbackKahler hι omega hpull).form) u hu' :=
  ⟨PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential _ _ hu one_pos,
    _, SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul _ hu one_pos⟩

/-- **Source `lma:posmasscurrres`, one member.** If `s ≤ φ`, `s ∈ PSH(X, θ - δω)` (so
`θ_s` is a Kähler current), `φ ∈ PSH(X, θ)` and `s|_V ≢ -∞`, then
`φ|_V ∈ PSH(V, θ|_V)` and `∫_V (θ|_V + dd^c φ|_V)^k > 0`. -/
theorem hasPositivePotentialMass_comp_of_le (omega : KahlerBackground n M)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    {θ : ClosedRealOneOneForm n M} {δ : ℝ} (hδ : 0 < δ) {φ s : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hs : IsThetaPshPotential (θ - δ • omega.form).val s)
    (hsφ : s ≤ φ) (hne : ∃ y, s (ι y) ≠ ⊥) :
    ∃ hφV : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val (fun y => φ (ι y)),
      HasPositivePotentialMass (ClosedRealOneOneForm.pullback hι θ) (fun y => φ (ι y)) hφV := by
  let ρ := pullbackKahler hι omega hpull
  have hsV := isThetaPshPotential_comp hι hs hne
  rw [pullback_sub_smul] at hsV
  have hsθ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val (fun y => s (ι y)) := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hsV
      (KahlerDomination.isSemipositive_smul ρ.isSemipositive hδ.le)
    rwa [show ρ.form = ClosedRealOneOneForm.pullback hι omega.form from rfl, sub_add_cancel] at h
  have hφV := isThetaPshPotential_comp hι hφ (exists_ne_bot_of_le hsφ hne)
  refine ⟨hφV, ?_⟩
  have hpos := RestrictedApproximantMass.diagonalPotentialMass_pos_of_sub_smul ρ hδ hsV hsθ
  exact hpos.trans_le (diagonalPotentialMass_mono_of_kahler ρ hsθ hφV
    (MoreSingularOn.of_le fun y _ => hsφ (ι y)))


omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V] in
/-- Potentials of `θ|_V` are potentials of `θ|_V + 1 • ω|_V`. -/
theorem isThetaPshPotential_add_kahler (omega : KahlerBackground n M)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    {θ : ClosedRealOneOneForm n M} {u : V → EReal}
    (hu : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val u) :
    IsThetaPshPotential
      (ClosedRealOneOneForm.pullback hι θ + (1 : ℝ) • (pullbackKahler hι omega hpull).form).val u :=
  LocalPotentials.isThetaPshPotential_add_of_semipositive hu
    (KahlerDomination.isSemipositive_smul (pullbackKahler hι omega hpull).isSemipositive
      zero_le_one)

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- Restriction of a potential of `θ + 1 • ω`. -/
theorem isThetaPshPotential_comp_add_kahler (omega : KahlerBackground n M)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    {θ : ClosedRealOneOneForm n M} {e : M → EReal}
    (he : IsThetaPshPotential (θ + (1 : ℝ) • omega.form).val e) (hne : ∃ y, e (ι y) ≠ ⊥) :
    IsThetaPshPotential
      (ClosedRealOneOneForm.pullback hι θ + (1 : ℝ) • (pullbackKahler hι omega hpull).form).val
      (fun y => e (ι y)) := by
  have h := isThetaPshPotential_comp hι he hne
  rwa [pullback_add_kahler hι omega hpull] at h

/-- **Source `lma:Igoodrest`, the member half.** Let `φ_j ↓`, `φ ≤ φ_j`, all in `PSH(X,θ)`,
and let `η_m ∈ PSH(X, θ + ω)` be barriers: for every `m` some `j` has
`t_m φ_j + (1 - t_m) η_m ≤ φ`, `t_m = 1 - (m+2)⁻¹`. If `φ|_V ≢ -∞` and `η_m|_V ≢ -∞` for all
`m`, then `φ_j|_V, φ|_V ∈ PSH(V, θ|_V)` and `φ_j|_V → φ|_V` in `d_S`. -/
theorem tendstoSingularityType_comp_of_barriers (omega : KahlerBackground n M)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (omegaV : KahlerBackground k V) {θ : ClosedRealOneOneForm n M}
    {φs : ℕ → M → EReal} {φ : M → EReal}
    (hφs : ∀ j, IsThetaPshPotential θ.val (φs j)) (hφ : IsThetaPshPotential θ.val φ)
    (hle : ∀ j, φ ≤ φs j) (hanti : ∀ x, Antitone fun j => φs j x)
    {η : ℕ → M → EReal} (hη : ∀ m, IsThetaPshPotential (θ + (1 : ℝ) • omega.form).val (η m))
    (hbar : ∀ m : ℕ, ∃ j, convexComb (1 - ((m : ℝ) + 2)⁻¹) (φs j) (η m) ≤ φ)
    (hne : ∃ y, φ (ι y) ≠ ⊥) (hηne : ∀ m, ∃ y, η m (ι y) ≠ ⊥) :
    (∀ j, IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
        (fun y => φs j (ι y))) ∧
      IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val (fun y => φ (ι y)) ∧
      TendstoSingularityType omegaV (fun j y => φs j (ι y)) (fun y => φ (ι y)) := by
  let ρ := pullbackKahler hι omega hpull
  have hφV := isThetaPshPotential_comp hι hφ hne
  have hφsV : ∀ j, IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
      (fun y => φs j (ι y)) := fun j =>
    isThetaPshPotential_comp hι (hφs j) (exists_ne_bot_of_le (hle j) hne)
  obtain ⟨hσbig, hφσ, hφpos⟩ := positive_of_add_kahler hι omega hpull hφV
  have hφsσ := fun j => isThetaPshPotential_add_kahler hι omega hpull (hφsV j)
  have hηV := fun m => isThetaPshPotential_comp_add_kahler hι omega hpull (hη m) (hηne m)
  have hmass := tendsto_mass_of_barriers ρ hφσ hφsσ (fun j y => hle j (ι y))
    (fun y => hanti (ι y)) (fun m => by
      obtain ⟨j, hj⟩ := hbar m
      exact ⟨j, _, hηV m, fun y => hj (ι y)⟩)
  have hlim := (SingularCanonicalSingularityOrderedMassCriterion.tendsto_native_iff_diagonalPotentialMass_of_le
    omegaV _ hσbig atTop (fun j => ⟨_, hφsσ j⟩) ⟨_, hφσ⟩ (fun j y => hle j (ι y)) hφpos).mpr
    hmass
  exact ⟨hφsV, hφV, tendstoSingularityType_of_tendsto omegaV hσbig hφsσ hφσ hlim⟩

/-- **Source `prop:varphiP_rest_gen`, the member half for `u ∼_P P_θ[u]`.** Let
`u ∈ PSH(X,θ)` and `e_m ∈ PSH(X,θ)` with `t_m P_θ[u] + (1 - t_m) e_m ≤ u`. If `u|_V ≢ -∞` and
`e_m|_V ≢ -∞` for all `m`, then `u|_V ∼_P (P_θ[u])|_V`. -/
theorem sourcePEquivalent_comp_singularityEnvelope [CompactSpace M] (omega : KahlerBackground n M)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    {e : ℕ → M → EReal} (he : ∀ m, IsThetaPshPotential θ.val (e m))
    (hbar : ∀ m : ℕ, convexComb (1 - ((m : ℝ) + 2)⁻¹) (singularityEnvelope θ.val u) (e m) ≤ u)
    (hne : ∃ y, u (ι y) ≠ ⊥) (hene : ∀ m, ∃ y, e m (ι y) ≠ ⊥) :
    SourcePEquivalent (n := k) (fun y => u (ι y))
      (fun y => singularityEnvelope θ.val u (ι y)) := by
  have : Nonempty M := ⟨ι (Classical.arbitrary V)⟩
  let ρ := pullbackKahler hι omega hpull
  have hv : IsThetaPshPotential θ.val (singularityEnvelope θ.val u) :=
    FirstPass.singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu
  have huv : MoreSingularOn u (singularityEnvelope θ.val u) univ :=
    moreSingularOn_singularityEnvelope hu
  have huV := isThetaPshPotential_comp hι hu hne
  have hvV := isThetaPshPotential_comp hι hv (exists_ne_bot_of_moreSingularOn huv hne)
  obtain ⟨_, huσ, hupos⟩ := positive_of_add_kahler hι omega hpull huV
  obtain ⟨_, hvσ, hvpos⟩ := positive_of_add_kahler hι omega hpull hvV
  have heV := fun m => isThetaPshPotential_add_kahler hι omega hpull
    (isThetaPshPotential_comp hι (he m) (hene m))
  have hmass := mass_eq_of_barriers ρ huσ hvσ (moreSingularOn_comp huv)
    (fun m => ⟨_, heV m, fun y => hbar m (ι y)⟩)
  have hord : SourcePOrder (n := k) (fun y => u (ι y))
      (fun y => singularityEnvelope θ.val u (ι y)) :=
    sourcePOrder_of_moreSingularOn ρ _ _ huσ hvσ (moreSingularOn_comp huv)
  exact (sourcePEquivalent_iff_diagonalPotentialMass_eq_of_sourcePOrder ρ _ huσ hvσ hupos hvpos
    hord).mpr hmass

/-- **Source `prop:varphiP_rest_gen`, the member half.** Let `φ, ψ ∈ PSH(X,θ)` with
`P_θ[φ] ≤ P_θ[ψ]`, and `e_m ∈ PSH(X,θ)` barriers for `ψ` as in
`sourcePEquivalent_comp_singularityEnvelope`. If `φ|_V`, `ψ|_V`, `e_m|_V ≢ -∞`, then
`φ|_V ⪯_P ψ|_V`. -/
theorem sourcePOrder_comp_of_barriers [CompactSpace M] (omega : KahlerBackground n M)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    {θ : ClosedRealOneOneForm n M} {φ ψ : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hψ : IsThetaPshPotential θ.val ψ) (hP : POrderWith θ φ ψ)
    {e : ℕ → M → EReal} (he : ∀ m, IsThetaPshPotential θ.val (e m))
    (hbar : ∀ m : ℕ, convexComb (1 - ((m : ℝ) + 2)⁻¹) (singularityEnvelope θ.val ψ) (e m) ≤ ψ)
    (hφne : ∃ y, φ (ι y) ≠ ⊥) (hψne : ∃ y, ψ (ι y) ≠ ⊥) (hene : ∀ m, ∃ y, e m (ι y) ≠ ⊥) :
    SourcePOrder (n := k) (fun y => φ (ι y)) (fun y => ψ (ι y)) := by
  have : Nonempty M := ⟨ι (Classical.arbitrary V)⟩
  let ρ := pullbackKahler hι omega hpull
  have hv : IsThetaPshPotential θ.val (singularityEnvelope θ.val ψ) :=
    FirstPass.singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hψ.1.hasSmoothLocalPotentials ψ hψ
  have hφv : MoreSingularOn φ (singularityEnvelope θ.val ψ) univ := by
    obtain ⟨C, hC⟩ := moreSingularOn_singularityEnvelope hφ
    exact ⟨C, fun x hx => (hC x hx).trans (add_le_add_left (hP x) _)⟩
  have hφV := isThetaPshPotential_comp hι hφ hφne
  have hvV := isThetaPshPotential_comp hι hv (exists_ne_bot_of_moreSingularOn hφv hφne)
  have h1 : SourcePOrder (n := k) (fun y => φ (ι y))
      (fun y => singularityEnvelope θ.val ψ (ι y)) :=
    sourcePOrder_of_moreSingularOn ρ _ _ hφV hvV (moreSingularOn_comp hφv)
  have h2 := (sourcePEquivalent_comp_singularityEnvelope hι omega hpull hψ he hbar hψne hene).2
  exact SourcePOrder.trans ρ h1 h2

omit [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V]
  [ConnectedSpace V] in
/-- `ν(u, V) = 0` as soon as `u|_V ≢ -∞` (positive Lelong numbers force poles). -/
theorem sourceGenericLelongNumber_eq_zero (hn : n ≠ 0) {θ : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) (hne : ∃ y, u (ι y) ≠ ⊥) :
    sourceGenericLelongNumber (n := n) ι u = 0 := by
  obtain ⟨y, hy⟩ := hne
  have hzero : lelongNumber (n := n) u (ι y) = 0 := by
    by_contra h
    exact hy (eq_bot_of_lelongNumber_pos (Nat.pos_of_ne_zero hn) hu.1 (pos_iff_ne_zero.mpr h))
  apply (nativeGeneric_zero_iff_source hn ι u).mp
  exact le_antisymm ((iInf_le _ y).trans_eq hzero) bot_le

/-- **A restriction which is the `d_S`-limit of the restricted approximation is a trace
operator** (`def:traceop`): if `(U_j)` is a quasi-equisingular approximation of `u` with
`U_j ∈ PSH(X,θ)`, `u|_V ≢ -∞` and `U_j|_V → u|_V` in `d_S`, then `u|_V` is a trace operator
of `u` along `V`. -/
theorem isSourceTraceRepresentativeAlong_comp_of_tendsto (hn : n ≠ 0)
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} {ε : ℕ → ℝ} {U : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega θ u ε U)
    (hU : ∀ j, IsThetaPshPotential θ.val (U j)) (hne : ∃ y, u (ι y) ≠ ⊥)
    (hconv : TendstoSingularityType omegaV (fun j y => U j (ι y)) (fun y => u (ι y))) :
    IsSourceTraceRepresentativeAlong omega omegaV hι u (fun y => u (ι y)) := by
  have hgeneric := sourceGenericLelongNumber_eq_zero (ι := ι) hn happ.target hne
  obtain ⟨C, hC, hadm, -⟩ :=
    AdmissibleTraceBackgroundMargin.exists_admissible_background_with_uniform_margin hι omega
      omegaV θ happ.error_antitone
  let β : KahlerBackground k V := KahlerBackground.smul hC omegaV
  have hdom : (β.form - ClosedRealOneOneForm.pullback hι θ).val.IsSemipositive := by
    have h : β.form - ClosedRealOneOneForm.pullback hι θ =
        (β.form - ClosedRealOneOneForm.pullback hι (θ + ε 0 • omega.form)) +
          ε 0 • ClosedRealOneOneForm.pullback hι omega.form := by
      rw [NefCoreKahlerCurrent.pullback_add_smul]
      abel
    rw [h]
    exact isSemipositive_add (hadm.2 0)
      (KahlerDomination.isSemipositive_smul
        (ClosedRealOneOneForm.pullback_isSemipositive hι omega.isSemipositive)
        (happ.error_nonneg 0))
  have hle : ∀ j, u ≤ U j := fun j x => (happ.term_antitone x).le_of_tendsto (happ.term_tendsto x) j
  have hτ : IsThetaPshPotential β.form.val (fun y => u (ι y)) :=
    isThetaPshPotential_of_sub_isSemipositive (isThetaPshPotential_comp hι happ.target hne) hdom
  have hterms : ∀ j, IsThetaPshPotential β.form.val (fun y => U j (ι y)) := fun j =>
    isThetaPshPotential_of_sub_isSemipositive
      (isThetaPshPotential_comp hι (hU j) (exists_ne_bot_of_le (hle j) hne)) hdom
  exact ⟨hgeneric, θ, ε, U, happ, β, hadm, hτ, hterms,
    hconv β.form (isBigClass_kahler β) hterms hτ⟩

/-- **Trace operators are closed under `P`-equivalence** (they are `d_S`-limits, hence defined
up to `d_S`-distance zero, `prop:ds0char`): if `τ` is a trace operator of `u` along `V` and
`τ' ∼_P τ` is quasi-psh on `V`, then `τ'` is a trace operator of `u` along `V`. -/
theorem isSourceTraceRepresentativeAlong_of_sourcePEquivalent (omega : KahlerBackground n M)
    (omegaV : KahlerBackground k V) {u : M → EReal} {τ τ' : V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omega omegaV hι u τ)
    {σ : ClosedRealOneOneForm k V} (hτ' : IsThetaPshPotential σ.val τ')
    (heq : SourcePEquivalent (n := k) τ τ') :
    IsSourceTraceRepresentativeAlong omega omegaV hι u τ' := by
  obtain ⟨hg, θ, ε, U, happ, β₀, hadm, hτ, hterms, hlim⟩ := htrace
  obtain ⟨D, hD, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omegaV (-σ)
  let β : KahlerBackground k V := β₀.add (KahlerBackground.smul hD omegaV)
  have hβform : β.form = β₀.form + D • omegaV.form := rfl
  have hDsemi : (D • omegaV.form).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul omegaV.isSemipositive hD.le
  have henl {w : V → EReal} (hw : IsThetaPshPotential β₀.form.val w) :
      IsThetaPshPotential β.form.val w :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hw hDsemi
  have hadm' : IsAdmissibleTraceBackground hι omega θ ε β.form := by
    refine ⟨β.isKahler, fun j => ?_⟩
    have h : β.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) =
        (β₀.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form)) +
          D • omegaV.form := by
      rw [hβform]
      abel
    change (β.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form)).val.IsSemipositive
    rw [h]
    exact isSemipositive_add (hadm.2 j) hDsemi
  have hτ'β : IsThetaPshPotential β.form.val τ' := by
    apply isThetaPshPotential_of_sub_isSemipositive hτ'
    have h : β.form - σ = β₀.form + (-σ + D • omegaV.form) := by
      rw [hβform]
      abel
    rw [h]
    exact isSemipositive_add β₀.isSemipositive hsemi
  have hlimβ := (SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds omegaV
    β₀.form β.form (isBigClass_kahler β₀) (isBigClass_kahler β) atTop hterms hτ
    (fun j => henl (hterms j)) (henl hτ)).mp hlim
  have hzero := (SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
    omegaV β.form (isBigClass_kahler β) (henl hτ) hτ'β).mpr heq
  refine ⟨hg, θ, ε, U, happ, β, hadm', hτ'β, fun j => henl (hterms j), ?_⟩
  let := singularityPseudoMetricSpace omegaV β.form (isBigClass_kahler β)
  let : TopologicalSpace (ThetaPshL1 β.form.val) :=
    (singularityPseudoMetricSpace omegaV β.form (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace
  let x : ℕ → ThetaPshL1 β.form.val := fun j => ⟨fun y => U j (ι y), henl (hterms j)⟩
  let a : ThetaPshL1 β.form.val := ⟨τ, henl hτ⟩
  let b : ThetaPshL1 β.form.val := ⟨τ', hτ'β⟩
  have ha : Tendsto x atTop (𝓝 a) := hlimβ
  change Tendsto x atTop (𝓝 b)
  have hab : dist a b = 0 := by
    rw [dist_eq_singularityDistance_toReal]
    change (singularityDistance omegaV β.form (isBigClass_kahler β) τ τ').toReal = 0
    rw [hzero, EReal.toReal_zero]
  rw [tendsto_iff_dist_tendsto_zero] at ha ⊢
  refine squeeze_zero (fun _ => dist_nonneg) (fun j => ?_) ha
  calc dist (x j) b ≤ dist (x j) a + dist a b := dist_triangle _ _ _
    _ = dist (x j) a := by rw [hab, add_zero]

end Target

/-! ### The ambient halves -/

section Ambient

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M]

/-- **Source `lma:Igoodrest`, the ambient half** (`lma:pathoenvelope`). Let `θ` be big,
`φ_j, φ ∈ PSH(X,θ)`, `φ ≤ φ_j` and `φ_j → φ` in `d_S`. Then there are `η_m ∈ PSH(X, θ + ω)`
such that for every `m` some `j` has `t_m φ_j + (1 - t_m) η_m ≤ φ`, `t_m = 1 - (m+2)⁻¹`. -/
theorem exists_barriers_of_tendsto (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {φs : ℕ → M → EReal} {φ : M → EReal}
    (hφs : ∀ j, IsThetaPshPotential θ.val (φs j)) (hφ : IsThetaPshPotential θ.val φ)
    (hle : ∀ j, φ ≤ φs j)
    (hlim : Tendsto (fun j => (⟨φs j, hφs j⟩ : ThetaPshL1 θ.val)) atTop
      (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace ⟨φ, hφ⟩)) :
    ∃ η : ℕ → M → EReal, (∀ m, IsThetaPshPotential (θ + (1 : ℝ) • omega.form).val (η m)) ∧
      ∀ m : ℕ, ∃ j, convexComb (1 - ((m : ℝ) + 2)⁻¹) (φs j) (η m) ≤ φ := by
  have hsemi : ((1 : ℝ) • omega.form).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul omega.isSemipositive zero_le_one
  have hφ' := LocalPotentials.isThetaPshPotential_add_of_semipositive hφ hsemi
  have hφs' := fun j => LocalPotentials.isThetaPshPotential_add_of_semipositive (hφs j) hsemi
  have hbig' := PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ hφ
    one_pos
  have hpos : HasPositivePotentialMass (θ + (1 : ℝ) • omega.form) φ hφ' :=
    SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul omega hφ one_pos
  have hlim' := (SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds omega θ
    (θ + (1 : ℝ) • omega.form) hbig hbig' atTop hφs hφ hφs' hφ').mp hlim
  have hmass := (SingularCanonicalSingularityOrderedMassCriterion.tendsto_native_iff_diagonalPotentialMass_of_le
    omega _ hbig' atTop (fun j => ⟨_, hφs' j⟩) ⟨_, hφ'⟩ hle hpos).mp hlim'
  set L := diagonalPotentialMass (θ + (1 : ℝ) • omega.form) φ hφ' with hL
  have hLtop : L ≠ ⊤ := (MixedMass.globalMixedMass_lt_top omega (fun _ : Fin n => hφ'.1)).ne
  have hmono : ∀ j, L ≤ diagonalPotentialMass (θ + (1 : ℝ) • omega.form) (φs j) (hφs' j) :=
    fun j => diagonalPotentialMass_mono_of_kahler omega hφ' (hφs' j)
      (MoreSingularOn.of_le fun x _ => hle j x)
  have key : ∀ m : ℕ, ∃ j, ∃ e : M → EReal,
      IsThetaPshPotential (θ + (1 : ℝ) • omega.form).val e ∧
        convexComb (1 - ((m : ℝ) + 2)⁻¹) (φs j) e ≤ φ := by
    intro m
    have hsub := ENNReal.Tendsto.sub hmass (tendsto_const_nhds (x := L)) (Or.inl hLtop)
    rw [tsub_self] at hsub
    have hmul := ENNReal.Tendsto.const_mul hsub
      (Or.inr (ENNReal.ofReal_ne_top (r := ((m : ℝ) + 2) ^ n)))
    rw [mul_zero] at hmul
    obtain ⟨j, hj⟩ := (hmul.eventually (gt_mem_nhds hpos)).exists
    have ha : ConvexCombEnvelopeMass.IsAdmissibleWeight n L
        (diagonalPotentialMass (θ + (1 : ℝ) • omega.form) (φs j) (hφs' j)) ((m : ℝ) + 2) :=
      ⟨by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith, hj.trans_le (hmono j)⟩
    obtain ⟨hE, -, -, hbarE⟩ := POrderAffineRooftop.xiaTheorem611 omega _ hφ' (hφs' j) hpos
      (pOrderWith_of_moreSingular (MoreSingularOn.of_le fun x _ => hle j x)) ha
    refine ⟨j, _, hE, ?_⟩
    rw [convexComb_swap] at hbarE
    exact hbarE
  choose j e he hbar using key
  exact ⟨e, he, fun m => ⟨j m, hbar m⟩⟩

/-- **Source `prop:varphiP_rest_gen`, the ambient half** (`lma:pathoenvelope` in the
equal-mass case). For `u ∈ PSH(X,θ)_{>0}` there are `e_m ∈ PSH(X,θ)` with
`t_m P_θ[u] + (1 - t_m) e_m ≤ u`. -/
theorem exists_envelope_barriers (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) (hpos : HasPositivePotentialMass θ u hu) :
    ∃ e : ℕ → M → EReal, (∀ m, IsThetaPshPotential θ.val (e m)) ∧
      ∀ m : ℕ, convexComb (1 - ((m : ℝ) + 2)⁻¹) (singularityEnvelope θ.val u) (e m) ≤ u := by
  have hv : IsThetaPshPotential θ.val (singularityEnvelope θ.val u) :=
    FirstPass.singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu
  have hmass := singularityEnvelopeMassPreserving omega θ u hu hv
  have hP : POrderWith θ u (singularityEnvelope θ.val u) :=
    pOrderWith_of_moreSingular (moreSingularOn_singularityEnvelope hu)
  have key : ∀ m : ℕ, ∃ e : M → EReal, IsThetaPshPotential θ.val e ∧
      convexComb (1 - ((m : ℝ) + 2)⁻¹) (singularityEnvelope θ.val u) e ≤ u := by
    intro m
    have ha : ConvexCombEnvelopeMass.IsAdmissibleWeight n (diagonalPotentialMass θ u hu)
        (diagonalPotentialMass θ (singularityEnvelope θ.val u) hv) ((m : ℝ) + 2) := by
      rw [hmass]
      exact ConvexCombEnvelopeMass.isAdmissibleWeight_of_eq hpos
        (by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith)
    obtain ⟨hE, -, -, hbarE⟩ := POrderAffineRooftop.xiaTheorem611 omega θ hu hv hpos hP ha
    refine ⟨_, hE, ?_⟩
    rw [convexComb_swap] at hbarE
    exact hbarE
  choose e he hbar using key
  exact ⟨e, he, hbar⟩

end Ambient

end SGPT.Trace.BertiniGeneral

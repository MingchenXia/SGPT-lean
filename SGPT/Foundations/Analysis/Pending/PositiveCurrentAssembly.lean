import SGPT.Foundations.Analysis.Pending.PositiveCurrentSecondLevel
import SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier
import SGPT.Foundations.Analysis.Pending.PositiveCurrentRooftop
import SGPT.Foundations.Analysis.Pending.PositiveCurrentIdealComparison
import SGPT.Foundations.Analysis.Pending.AmbientMassBackgroundMonotone
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof
import SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierModelReduction
import SGPT.Foundations.Analysis.Pending.Copy4TraceInputReduction
import SGPT.Foundations.Analysis.FirstPass.KahlerCurrentPerturbation
import SGPT.Foundations.Analysis.Pending.SkodaIntegrability
import SGPT.Foundations.Analysis.Pending.MinimalSingularityLelongVanishing

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 `sec:positive-current`: `PositiveCurrentInput` from the trace package and `lem:domination`

Source: Copy-4, `sec:setup` ("The trace of `V_θ`", `sec:trace-approx`) and `sec:positive-current`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1398-1712`).

This module assembles the route-independent pieces of the positive-current programme
(`scratch/tn23-envelopes-qea-plan-0117.md` §5) into `Copy4TraceInputReduction.PositiveCurrentInput`.
What remains are exactly two inputs, both stated here as `Prop`s and taken as hypotheses (nothing is
assumed as an interface):

* `HasTracePackage` — the properties Copy-4 uses of the trace `u = Tr^θ_V(V_θ)` (plan §5.1): a
  quasi-equisingular approximation `Φ_j` of `V_θ` (Demailly's, with its global type and positive
  errors `ε_j`), with restrictions `φ_j = Φ_j|_V ∈ PSH(V, β_j)`, `β_j = γ + ε_j ω_V`, and a
  `γ`-psh `u` on `V` with
  (T1) `∫_V γ_u^k > 0`, (T3) `∫_V (β_j)_{φ_j}^k → ∫_V γ_u^k`, (T2) `u ≤ P_{β_j}[φ_j] + C_j` for all
  large `j`.  (T4), `𝓘(cu) ⊆ Res_V 𝓘(cV_θ)`, is DERIVED (`PositiveCurrentTraceMultiplier`).  Both
  routes produce this package: the trace operator (route T) and the trace-free limit
  `u = lim_j P_{β_j}[φ_j]` (route F).
* `DominationLemma` — Copy-4 `lem:domination` on `(V, ω_V, γ)`: for every `h₀ > 0` a `δ_* > 0`
  such that every `v ∈ PSH(V, γ + ηω_V)`, `0 ≤ η ≤ 1`, of mass `≥ h₀` is `I`-dominated by a
  current `γ + ηω_V + ddᶜs ≥ δ_* ω_V`.  (Copy-4 also assumes `{γ}` big; the proof does not use it,
  the mass bound being what matters, so the statement here omits it.)

`positiveCurrentInput_of_tracePackage` follows Copy-4: for given `C`, a dyadic level `m = 2^j` is
chosen (admissible weight `2C`, `ε_j ≤ min(1, δ_*/2)`, `b_j ≥ h/2`, (T2) at `j`);
`lem:positive-rooftop` (`PositiveCurrentRooftop`, Lemma 2.4.4 for the big class `β_j`) gives `h_C`;
`lem:domination` gives `K = γ + ddᶜφ_K ≥ (δ_*/2)ω_V` with `K ≼_I h_C`; `lem:ideal-comparison`
(TN-CLASSICAL's `PositiveCurrentIdealComparison` for the first inclusion, (T4) for the second)
gives `𝓘(ℓφ_K)·𝔅̄_m^{(C-1)r} ⊆ 𝔅̄_{Cℓ}` for every dyadic `r`, `ℓ = mr`; and the second level
(`PositiveCurrentSecondLevel`) gives the clause of `PositiveCurrentInput` with `δ₀ = δ_*/4`.

Sorry-free.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.PositiveCurrentAssembly

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.HolomorphicIdealSheaves
  FirstPass.GlobalAnalyticSingularities FirstPass.BlowupSequences
  FirstPass.QuasiEquisingularApproximation FirstPass.IEnvelope
  SubmanifoldChartedSpace SubmanifoldIdealRestriction SubmanifoldMassCalculus
  DiagonalMass IdealWeightPowers Copy4TraceInputReduction

/-! ### `lem:domination` as a statement -/

section Domination

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z] [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z]

/-- The conclusion of Copy-4 `lem:domination` for given `h₀` and `δ`: every `v ∈ PSH(Z, γ + ηω)`,
`0 ≤ η ≤ 1`, with `∫(γ + ηω)_v^k ≥ h₀` is `I`-dominated (`IOrderOnManifold`) by the potential `s`
of a current `γ + ηω + ddᶜs ≥ δω`. -/
def DominationProperty (omegaZ : KahlerBackground k Z) (γ : ClosedRealOneOneForm k Z)
    (h₀ : ℝ≥0∞) (δ : ℝ) : Prop :=
  ∀ η : ℝ, 0 ≤ η → η ≤ 1 → ∀ (v : Z → EReal) (hv : IsThetaPshPotential (γ + η • omegaZ.form).val v),
    h₀ ≤ diagonalPotentialMass (γ + η • omegaZ.form) v hv →
    ∃ s : Z → EReal, IsThetaPshPotential (γ + η • omegaZ.form - δ • omegaZ.form).val s ∧
      IOrderOnManifold (n := k) s v

/-- **Copy-4 `lem:domination`** (statement): for every `h₀ > 0` there is a `δ_* > 0`, independent
of `η` and `v`, with `DominationProperty`. -/
def DominationLemma (omegaZ : KahlerBackground k Z) (γ : ClosedRealOneOneForm k Z) : Prop :=
  ∀ h₀ : ℝ≥0∞, 0 < h₀ → ∃ δ : ℝ, 0 < δ ∧ DominationProperty omegaZ γ h₀ δ

end Domination

/-! ### Bigness of `γ + εω` from a `γ`-psh potential -/

section Bigness

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z]

/-- `γ + εω` is big as soon as `γ` admits a potential: `γ + ddᶜu ≥ 0` gives the Kähler current
`γ + εω + ddᶜu ≥ εω`. -/
theorem isBigClass_add_smul_of_isThetaPshPotential (omegaZ : KahlerBackground k Z)
    (γ : ClosedRealOneOneForm k Z) {u : Z → EReal} (hu : IsThetaPshPotential γ.val u) {ε : ℝ}
    (hε : 0 < ε) : IsBigClass (RealBottChern.ofRepresentative (γ + ε • omegaZ.form)) := by
  refine ⟨⟨γ + ε • omegaZ.form, rfl, u, KahlerBackground.smul hε omegaZ, ?_⟩⟩
  rw [KahlerBackground.smul_form, add_sub_cancel_right]
  exact hu

end Bigness

/-! ### Extended-real bookkeeping -/

/-- From `h + rψ ≤ Cu` and `φ ≤ ψ + c` (`r ≥ 0`, `c` real): `(h - rc) + rφ ≤ Cu`. -/
theorem add_neg_mul_add_mul_le {r c : ℝ} (hr : 0 ≤ r) {h ψ φ U : EReal}
    (hroof : h + (r : EReal) * ψ ≤ U) (hφψ : φ ≤ ψ + (c : EReal)) :
    h + ((-(r * c) : ℝ) : EReal) + (r : EReal) * φ ≤ U := by
  have hA : (r : EReal) * φ ≤ (r : EReal) * ψ + ((r * c : ℝ) : EReal) := by
    rcases hr.eq_or_lt with hr0 | hrpos
    · subst hr0; simp
    · calc (r : EReal) * φ ≤ (r : EReal) * (ψ + (c : EReal)) :=
            mul_le_mul_of_nonneg_left hφψ (EReal.coe_nonneg.mpr hr)
        _ = (r : EReal) * ψ + ((r * c : ℝ) : EReal) :=
            ThetaPshConvexCombination.coe_mul_add_coe hrpos ψ c
  calc h + ((-(r * c) : ℝ) : EReal) + (r : EReal) * φ
      ≤ h + ((-(r * c) : ℝ) : EReal) + ((r : EReal) * ψ + ((r * c : ℝ) : EReal)) :=
        add_le_add le_rfl hA
    _ = (h + (r : EReal) * ψ) + (((-(r * c) : ℝ) : EReal) + ((r * c : ℝ) : EReal)) := by abel
    _ = h + (r : EReal) * ψ := by rw [← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]
    _ ≤ U := hroof

/-- `h ≤ (h - a) + a` for a real `a`. -/
theorem le_add_neg_add (h : EReal) (a : ℝ) :
    h ≤ h + ((-a : ℝ) : EReal) + (a : EReal) := by
  rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]


/-! ### `lem:positive-rooftop` + `lem:domination`: the Kähler current `K` -/

section KahlerCurrent

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z] [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z] [Nonempty Z]
  [ConnectedSpace Z]

/-- **Copy-4, from `lem:positive-rooftop` to `eq:def-K`.**  For `β = γ + εω`, `0 < ε ≤ 1`,
`2ε ≤ δ`, a `γ`-psh `u ≤ ψ` (`ψ` a `β`-potential) with `∫β_u^k > 0`, `2C` admissible, and
`h₀ ≤ 2^{-k}∫β_ψ^k`, `lem:positive-rooftop` gives `h_C ∈ PSH(Z, β)` with `h_C + (C-1)ψ ≤ Cu`,
and `lem:domination` (for `h₀`, `δ`) applied to `v = h_C` gives `s` with
`K = γ + ddᶜs ≥ (δ/2)ω` (`= K⁺ - εω`, `K⁺ ≥ δω`) and `K ≼_I h_C`. -/
theorem exists_rooftop_kahlerCurrent (omegaZ : KahlerBackground k Z)
    (γ : ClosedRealOneOneForm k Z) {u ψ : Z → EReal} (hu : IsThetaPshPotential γ.val u)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hεδ : 2 * ε ≤ δ)
    (hψ : IsThetaPshPotential (γ + ε • omegaZ.form).val ψ) (hle : u ≤ ψ)
    (hu' : IsThetaPshPotential (γ + ε • omegaZ.form).val u)
    (hpos : 0 < diagonalPotentialMass (γ + ε • omegaZ.form) u hu') {C : ℕ} (hC : 1 ≤ C)
    (hadm : ConvexCombEnvelopeMass.IsAdmissibleWeight k
      (diagonalPotentialMass (γ + ε • omegaZ.form) u hu')
      (diagonalPotentialMass (γ + ε • omegaZ.form) ψ hψ) ((2 * C : ℕ) : ℝ))
    {h₀ : ℝ≥0∞}
    (hh₀ : h₀ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) * diagonalPotentialMass (γ + ε • omegaZ.form) ψ hψ)
    (hD : DominationProperty omegaZ γ h₀ δ) :
    ∃ (h s : Z → EReal), IsThetaPshPotential (γ + ε • omegaZ.form).val h ∧
      (∀ x, h x + (((C - 1 : ℕ) : ℝ) : EReal) * ψ x ≤ ((C : ℝ) : EReal) * u x) ∧
      IsThetaPshPotential (γ + (-(δ / 2)) • omegaZ.form).val s ∧ IOrderOnManifold (n := k) s h := by
  obtain ⟨h, hh, hroof, hmass⟩ := PositiveCurrentRooftop.exists_positiveRooftop omegaZ
    (γ + ε • omegaZ.form) (isBigClass_add_smul_of_isThetaPshPotential omegaZ γ hu hε) hu' hψ hle
    hpos hC hadm
  obtain ⟨s, hs, hsI⟩ := hD ε hε.le hε1 h hh (hh₀.trans hmass)
  refine ⟨h, s, hh, hroof, ?_, hsI⟩
  have hsemi : ((δ / 2 - ε) • omegaZ.form).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul omegaZ.isSemipositive (by linarith)
  have h1 := LocalPotentials.isThetaPshPotential_add_of_semipositive hs hsemi
  have hform : γ + ε • omegaZ.form - δ • omegaZ.form + (δ / 2 - ε) • omegaZ.form =
      γ + (-(δ / 2)) • omegaZ.form := by module
  rwa [hform] at h1

end KahlerCurrent

/-! ### The trace package -/

section Package

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **The properties Copy-4 uses of the trace of `V_θ`** (plan §5.1), for `V` with its
flattening complex structure, the Borel structure, `γ = θ|_V`, `ω_V = ω|_V`: a quasi-equisingular
approximation `Φ_j` of `V_θ` of global type `(2^{-j}, 𝓘(2^jV_θ))` with positive errors `ε_j`, the
restrictions `φ_j ∈ PSH(V, γ + ε_jω_V)`, and a `γ`-psh `u` with (T1) positive mass, (T3)
`∫(γ + ε_jω_V)_{φ_j}^k → ∫γ_u^k`, (T2) `u ≤ P_{γ+ε_jω_V}[φ_j] + C_j` for all large `j`. -/
def HasTracePackage [CompactSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) : Prop :=
  letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
  haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
  letI : MeasurableSpace V.carrier := borel _
  haveI : BorelSpace V.carrier := ⟨rfl⟩
  haveI : CompactSpace V.carrier := compactSpace_of_isClosed hV.1
  ∃ (ε : ℕ → ℝ) (Φ : ℕ → X → EReal),
    IsQuasiEquisingularApproximation omega θ (thetaPshSupremum θ.val) ε Φ ∧ (∀ j, 0 < ε j) ∧
    (∀ j, HasAnalyticSingularitiesOfType (n := n) (Φ j) (((2 ^ j : ℕ) : ℚ)⁻¹)
      (multiplierIdeal (n := n) ((2 ^ j : ℕ) : ℝ) (thetaPshSupremum θ.val))) ∧
    ∃ (u : V.carrier → EReal)
      (hu : IsThetaPshPotential
        (ClosedRealOneOneForm.pullback
          (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ).val u)
      (hφ : ∀ j, IsThetaPshPotential
        (ClosedRealOneOneForm.pullback
            (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ +
          ε j • (SubmanifoldKahlerRestriction.kahlerBackground
            (le_of_isClosedConnectedSubmanifold hV) hV.2.2 omega).form).val
        (fun x : V.carrier => Φ j x.1)),
      0 < diagonalPotentialMass
        (ClosedRealOneOneForm.pullback
          (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ) u hu ∧
      Tendsto (fun j => diagonalPotentialMass
        (ClosedRealOneOneForm.pullback
            (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ +
          ε j • (SubmanifoldKahlerRestriction.kahlerBackground
            (le_of_isClosedConnectedSubmanifold hV) hV.2.2 omega).form)
        (fun x : V.carrier => Φ j x.1) (hφ j)) atTop
        (𝓝 (diagonalPotentialMass
          (ClosedRealOneOneForm.pullback
            (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ) u hu)) ∧
      ∀ᶠ j in atTop, ∃ C : ℝ, ∀ x : V.carrier,
        u x ≤ singularityEnvelope
          (ClosedRealOneOneForm.pullback
              (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ +
            ε j • (SubmanifoldKahlerRestriction.kahlerBackground
              (le_of_isClosedConnectedSubmanifold hV) hV.2.2 omega).form).val
          (fun x : V.carrier => Φ j x.1) x + (C : EReal)

/-- `lem:domination` on `(V, ω_V, γ)`, with `V`'s flattening complex structure and Borel
structure. -/
def HasDominationLemma [CompactSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) : Prop :=
  letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
  haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
  letI : MeasurableSpace V.carrier := borel _
  haveI : BorelSpace V.carrier := ⟨rfl⟩
  haveI : CompactSpace V.carrier := compactSpace_of_isClosed hV.1
  DominationLemma (SubmanifoldKahlerRestriction.kahlerBackground
      (le_of_isClosedConnectedSubmanifold hV) hV.2.2 omega)
    (ClosedRealOneOneForm.pullback (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ)

end Package

/-! ### The assembly -/

section Assembly

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **`PositiveCurrentInput` from the trace package and `lem:domination`** (Copy-4
`sec:positive-current`, route-independent).  See the module docstring for the order of the
choices; `δ₀ = δ_*/4` with `δ_*` from `lem:domination` at `h₀ = 2^{-k-1}∫γ_u^k`. -/
theorem positiveCurrentInput_of_tracePackage [CompactSpace X] (hn : 0 < n)
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) (hdim : 0 < V.dim)
    (hψ : IsThetaPshPotential θ.val (thetaPshSupremum θ.val))
    (hpkg : HasTracePackage omega θ V hV) (hdom : HasDominationLemma omega θ V hV) :
    PositiveCurrentInput omega θ V hV := by
  set hk := le_of_isClosedConnectedSubmanifold hV with hkdef
  let := chartedSpace hk hV.2.2
  have := isComplexManifold_chartedSpace hk hV.2.2
  let : MeasurableSpace V.carrier := borel _
  have : BorelSpace V.carrier := ⟨rfl⟩
  have : CompactSpace V.carrier := compactSpace_of_isClosed hV.1
  have : ConnectedSpace V.carrier := connectedSpace_of_isClosedConnectedSubmanifold hV
  have : Nonempty V.carrier := hV.2.1.nonempty.to_subtype
  set ωV := SubmanifoldKahlerRestriction.kahlerBackground hk hV.2.2 omega with hωV
  set γ := ClosedRealOneOneForm.pullback (contMDiff_val hk hV.2.2) θ with hγ
  obtain ⟨ε, Φ, hqea, hεpos, htypeX, u, hu, hφ, hLpos, hlim, hP⟩ := hpkg
  set L := diagonalPotentialMass γ u hu with hLdef
  have hLtop : L ≠ ⊤ :=
    (DiagonalMeasureRegularity.diagonalPotentialMeasure_lt_top ωV γ hu univ).ne
  -- `h₀ = 2^{-k} (L/2)` and `δ_*`
  set h₀ : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ V.dim) * (L / 2) with hh₀
  have hh₀pos : 0 < h₀ :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      (ENNReal.half_pos hLpos.ne').ne'
  obtain ⟨δ, hδ, hD⟩ := hdom h₀ hh₀pos
  intro C hC2
  have hC1 : 1 ≤ C := by omega
  -- the two sequences of masses
  have hu' : ∀ j, IsThetaPshPotential (γ + ε j • ωV.form).val u := fun j =>
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu
      (KahlerDomination.isSemipositive_smul ωV.isSemipositive (hεpos j).le)
  have ha : ∀ j, L ≤ diagonalPotentialMass (γ + ε j • ωV.form) u (hu' j) := fun j =>
    AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul ωV.isSemipositive
      (hεpos j) hu (hu' j)
  -- the level `j`
  have hE1 : ∀ᶠ j in atTop, ε j ≤ 1 ∧ 2 * ε j ≤ δ := by
    have h1 := hqea.error_tendsto.eventually (ge_mem_nhds zero_lt_one)
    have h2 := hqea.error_tendsto.eventually (ge_mem_nhds (half_pos hδ))
    filter_upwards [h1, h2] with j hj1 hj2
    exact ⟨hj1, by linarith⟩
  have hE2 : ∀ᶠ j in atTop, L / 2 ≤ diagonalPotentialMass (γ + ε j • ωV.form)
      (fun x : V.carrier => Φ j x.1) (hφ j) :=
    (hlim.eventually (lt_mem_nhds (ENNReal.half_lt_self hLpos.ne' hLtop))).mono
      fun _ h => h.le
  have h2C : (1 : ℝ) < ((2 * C : ℕ) : ℝ) := by
    have : 1 < 2 * C := by omega
    exact_mod_cast this
  have hE3 : ∀ᶠ j in atTop, ConvexCombEnvelopeMass.IsAdmissibleWeight V.dim
      (diagonalPotentialMass (γ + ε j • ωV.form) u (hu' j))
      (diagonalPotentialMass (γ + ε j • ωV.form) (fun x : V.carrier => Φ j x.1) (hφ j))
      ((2 * C : ℕ) : ℝ) :=
    PositiveCurrentRooftop.eventually_isAdmissibleWeight hLpos hLtop ha hlim h2C
  obtain ⟨j, ⟨hε1, hεδ⟩, hbj, hadm, Cj, hCj⟩ := (hE1.and (hE2.and (hE3.and hP))).exists
  set m : ℕ := 2 ^ j with hm
  set φm : V.carrier → EReal := fun x => Φ j x.1 with hφmdef
  set β := γ + ε j • ωV.form with hβ
  -- `ψ = P_β[φ_m] + C_j ≥ u`, of the mass of `φ_m`
  have hPpsh : IsThetaPshPotential β.val (singularityEnvelope β.val φm) :=
    singularityEnvelope_isThetaPshPotential β.val β.property.1 β.property.2
      (hφ j).1.hasSmoothLocalPotentials φm (hφ j)
  set ψ : V.carrier → EReal := fun x => singularityEnvelope β.val φm x + (Cj : EReal) with hψdef
  have hψpsh : IsThetaPshPotential β.val ψ := hPpsh.add_const Cj
  have hψmass : diagonalPotentialMass β ψ hψpsh = diagonalPotentialMass β φm (hφ j) := by
    rw [RooftopConvexCombBarrierModelReduction.diagonalPotentialMass_add_const β hPpsh Cj hψpsh]
    exact singularityEnvelopeMassPreserving ωV β φm (hφ j) hPpsh
  have hadm' : ConvexCombEnvelopeMass.IsAdmissibleWeight V.dim
      (diagonalPotentialMass β u (hu' j)) (diagonalPotentialMass β ψ hψpsh)
      ((2 * C : ℕ) : ℝ) := by
    rw [hψmass]; exact hadm
  -- `φ_m ≤ ψ + c`
  obtain ⟨c0, hc0⟩ := (hφ j).exists_normalized_singularityCompetitor
  have hφψ : ∀ x, φm x ≤ ψ x + ((c0 - Cj : ℝ) : EReal) := by
    intro x
    have h1 : φm x - (c0 : EReal) ≤ singularityEnvelope β.val φm x :=
      le_singularityEnvelope hc0.1.1 hc0.1.2 hc0.2 x
    have h2 : φm x ≤ singularityEnvelope β.val φm x + (c0 : EReal) :=
      (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot c0)) (.inl (EReal.coe_ne_top c0))).mp h1
    calc φm x ≤ singularityEnvelope β.val φm x + (c0 : EReal) := h2
      _ = ψ x + ((c0 - Cj : ℝ) : EReal) := by
        simp only [hψdef]
        rw [add_assoc, ← EReal.coe_add, add_sub_cancel]
  -- `lem:positive-rooftop` and `lem:domination`
  have hh₀le : h₀ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ V.dim) * diagonalPotentialMass β ψ hψpsh := by
    rw [hψmass, hh₀]
    exact mul_le_mul_of_nonneg_left hbj zero_le
  obtain ⟨hC_, s, hhC, hroof, hs, hsI⟩ := exists_rooftop_kahlerCurrent ωV γ hu (hεpos j) hε1 hεδ
    hψpsh (fun x => hCj x) (hu' j) (lt_of_lt_of_le hLpos (ha j)) hC1 hadm' hh₀le hD
  -- `K ≥ 2 δ₀ ω_V` with `δ₀ = δ/4`
  have hK : IsThetaPshPotential (ClosedRealOneOneForm.pullback (contMDiff_val hk hV.2.2)
      (θ - (2 * (δ / 4)) • omega.form)).val s := by
    have hθ : θ - (2 * (δ / 4)) • omega.form = θ + (-(δ / 2)) • omega.form := by module
    rw [hθ]
    exact (isThetaPshPotential_pullback_add_smul_iff hk hV.2.2 θ omega.form (-(δ / 2)) s).mpr hs
  -- the `I`-domination of `u` by the restricted approximants, for (T4)
  have hH : ∀ᶠ q in atTop, IOrderOnManifold (n := V.dim) u (fun x : V.carrier => Φ q x.1) :=
    hP.mono fun q ⟨Cq, hCq⟩ =>
      PositiveCurrentTraceMultiplier.iOrderOnManifold_of_le_singularityEnvelope_add
        (γ + ε q • ωV.form).property.1 (γ + ε q • ωV.form).property.2 (hφ q) hCq
  -- `lem:ideal-comparison` at every dyadic level `ℓ = m 2^i`
  have hideal : ∀ i : ℕ,
      ((multiplierIdeal (n := V.dim) ((m * 2 ^ i : ℕ) : ℝ) s).mul
          (idealPow (restrictIdeal (k := V.dim) (W := V.carrier)
            (multiplierIdeal (n := n) (m : ℝ) (thetaPshSupremum θ.val))) ((C - 1) * 2 ^ i))).Le
        (restrictIdeal (k := V.dim) (W := V.carrier)
          (multiplierIdeal (n := n) ((C * m * 2 ^ i : ℕ) : ℝ) (thetaPshSupremum θ.val))) := by
    intro i
    have hℓ : 0 < m * 2 ^ i := by positivity
    have hmpos : 0 < m := by positivity
    have hmp : m * ((C - 1) * 2 ^ i) = (m * 2 ^ i) * (C - 1) := by ring
    have htypeV : HasAnalyticSingularitiesOfType (n := V.dim) φm ((m : ℚ)⁻¹)
        (restrictIdeal (k := V.dim) (W := V.carrier)
          (multiplierIdeal (n := n) (m : ℝ) (thetaPshSupremum θ.val))) :=
      AnalyticTypeRestriction.hasAnalyticSingularitiesOfType_comp (contMDiff_val hk hV.2.2)
        (htypeX j)
    set r : ℝ := ((C - 1 : ℕ) : ℝ) with hr
    have hr0 : 0 ≤ r := Nat.cast_nonneg _
    set h' : V.carrier → EReal := fun x => hC_ x + ((-(r * (c0 - Cj)) : ℝ) : EReal) with hh'
    have hle' : ∀ z, h' z + (r : EReal) * φm z ≤ ((C : ℝ) : EReal) * u z := fun z =>
      add_neg_mul_add_mul_le hr0 (hroof z) (hφψ z)
    have hh'psh : IsThetaPshPotential β.val h' := hhC.add_const _
    have hIord : IOrderOnManifold (n := V.dim) s h' :=
      hsI.trans (Pending.iOrderOnManifold_of_le_add hh'psh.1.quasiPlurisubharmonic
        (C := r * (c0 - Cj)) fun x => le_add_neg_add (hC_ x) (r * (c0 - Cj)))
    have h𝔣 : (multiplierIdeal (n := V.dim) ((m * 2 ^ i : ℕ) : ℝ) s).Le
        (multiplierIdeal (n := V.dim) ((m * 2 ^ i : ℕ) : ℝ) h') :=
      PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold hIord
        (by exact_mod_cast hℓ)
    have h1 := PositiveCurrentIdealComparison.mul_idealPow_le_multiplierIdeal hC1 hℓ hmpos hmp
      hu.1.quasiPlurisubharmonic hle' htypeV h𝔣
    have h2 := PositiveCurrentTraceMultiplier.multiplierIdeal_le_restrictIdeal_of_eventually_iOrder
      hqea hk hV.2.2 hu.1.quasiPlurisubharmonic hH (c := ((C * (m * 2 ^ i) : ℕ) : ℝ))
      (by have : 0 < C * (m * 2 ^ i) := by positivity
          exact_mod_cast this)
    have hcast : C * (m * 2 ^ i) = C * m * 2 ^ i := by ring
    intro x g hg
    have h3 := h2 x g (h1 x g hg)
    rwa [hcast] at h3
  -- the second level and the encoding
  have hsl := PositiveCurrentSecondLevel.secondLevel_of_kahlerCurrent hn omega θ V hV hdim hψ.1
    (C := C) hm (by positivity : 0 < δ / 4) hK hideal
  exact ⟨m, Nat.one_le_two_pow, δ / 4, by positivity, hsl⟩

/-- **`PositiveCurrentInput` under the standing hypotheses of
`PositiveCurrentInputInterface.ct22Copy4_positiveCurrentInput`**, from the trace package and
`lem:domination`: bigness of `{θ}` makes `V_θ` a `θ`-psh potential. -/
theorem positiveCurrentInput_of_tracePackage_of_isBigClass [CompactSpace X]
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) (hdim_pos : 0 < V.dim)
    (hdim_lt : V.dim < n)
    (hpkg : HasTracePackage omega θ V hV) (hdom : HasDominationLemma omega θ V hV) :
    PositiveCurrentInput omega θ V hV := by
  obtain ⟨x, -⟩ := hV.2.1.nonempty
  have : Nonempty X := ⟨x⟩
  exact positiveCurrentInput_of_tracePackage (hdim_pos.trans hdim_lt) omega θ V hV hdim_pos
    (MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ hbig) hpkg hdom

end Assembly

/-! ### The trace package from its `u`-part -/

section UPart

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **The `u`-part of the trace package**: for EVERY quasi-equisingular approximation `Φ_j` of
`V_θ` of global type `(2^{-j}, 𝓘(2^jV_θ))` with positive errors and restrictions
`φ_j ∈ PSH(V, γ + ε_jω_V)`, a `γ`-psh `u` on `V` with (T1) `∫γ_u^k > 0`, (T3)
`∫(γ + ε_jω_V)_{φ_j}^k → ∫γ_u^k` and (T2) `u ≤ P_{γ+ε_jω_V}[φ_j] + C_j` for large `j`.  This is
the route-specific input: the trace-free limit `u = lim_j P_{γ+ε_jω_V}[φ_j]` (route F) satisfies
(T2) with `C_j = 0`; the trace operator (route T) is independent of the approximation. -/
def TraceUPart [CompactSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) : Prop :=
  letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
  haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
  letI : MeasurableSpace V.carrier := borel _
  haveI : BorelSpace V.carrier := ⟨rfl⟩
  haveI : CompactSpace V.carrier := compactSpace_of_isClosed hV.1
  ∀ (ε : ℕ → ℝ) (Φ : ℕ → X → EReal),
    IsQuasiEquisingularApproximation omega θ (thetaPshSupremum θ.val) ε Φ → (∀ j, 0 < ε j) →
    (∀ j, HasAnalyticSingularitiesOfType (n := n) (Φ j) (((2 ^ j : ℕ) : ℚ)⁻¹)
      (multiplierIdeal (n := n) ((2 ^ j : ℕ) : ℝ) (thetaPshSupremum θ.val))) →
    ∀ hφ : ∀ j, IsThetaPshPotential
        (ClosedRealOneOneForm.pullback
            (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ +
          ε j • (SubmanifoldKahlerRestriction.kahlerBackground
            (le_of_isClosedConnectedSubmanifold hV) hV.2.2 omega).form).val
        (fun x : V.carrier => Φ j x.1),
    ∃ (u : V.carrier → EReal)
      (hu : IsThetaPshPotential
        (ClosedRealOneOneForm.pullback
          (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ).val u),
      0 < diagonalPotentialMass
        (ClosedRealOneOneForm.pullback
          (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ) u hu ∧
      Tendsto (fun j => diagonalPotentialMass
        (ClosedRealOneOneForm.pullback
            (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ +
          ε j • (SubmanifoldKahlerRestriction.kahlerBackground
            (le_of_isClosedConnectedSubmanifold hV) hV.2.2 omega).form)
        (fun x : V.carrier => Φ j x.1) (hφ j)) atTop
        (𝓝 (diagonalPotentialMass
          (ClosedRealOneOneForm.pullback
            (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ) u hu)) ∧
      ∀ᶠ j in atTop, ∃ C : ℝ, ∀ x : V.carrier,
        u x ≤ singularityEnvelope
          (ClosedRealOneOneForm.pullback
              (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ +
            ε j • (SubmanifoldKahlerRestriction.kahlerBackground
              (le_of_isClosedConnectedSubmanifold hV) hV.2.2 omega).form).val
          (fun x : V.carrier => Φ j x.1) x + (C : EReal)

/-- **The Demailly half of the trace package is proved** (Copy-4 `sec:trace-approx`): under the
standing hypotheses (`{θ}` big, `V ⊄ E_nn(α)`), Demailly's approximation of `V_θ` and its
restrictions to `V` (`SubmanifoldMassCalculus.exists_restrictedApproximants`, the Skoda clause at a
point `x_* ∈ V \ E_nn(α)`) supply everything in `HasTracePackage` except the `u`-part. -/
theorem hasTracePackage_of_traceUPart [CompactSpace X] (hn : 0 < n)
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim)
    (hnonNef : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    (hU : TraceUPart omega θ V hV) : HasTracePackage omega θ V hV := by
  obtain ⟨x, hxV, hxnn⟩ := not_subset.mp hnonNef
  have : Nonempty X := ⟨x⟩
  have hψ := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ hbig
  have hskoda := SkodaIntegrability.not_subset_zeroLocus_multiplierIdeal_of_lelongNumber_eq_zero
    hψ.1 hxV (MinimalSingularityLelongVanishing.lelongNumber_thetaPshSupremum_eq_zero hn omega θ
      hbig hxnn)
  set hk := le_of_isClosedConnectedSubmanifold hV
  let := chartedSpace hk hV.2.2
  have := isComplexManifold_chartedSpace hk hV.2.2
  obtain ⟨ε, Φ, hqea, hεpos, htype⟩ :=
    QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation_ofType_pos hn
      omega θ hψ
  have hnz : ∀ j : ℕ, ¬ V.carrier ⊆
      (multiplierIdeal (n := n) ((2 ^ j : ℕ) : ℝ) (thetaPshSupremum θ.val)).zeroLocus :=
    fun j => hskoda (2 ^ j) Nat.one_le_two_pow
  have hφ := fun j => (isThetaPshPotential_pullback_add_smul_iff hk hV.2.2 θ omega.form (ε j)
    _).mp (isThetaPshPotential_comp_val hV (hqea.term j).1 (htype j) (hnz j)).1
  obtain ⟨u, hu, h1, h2, h3⟩ := hU ε Φ hqea hεpos htype hφ
  exact ⟨ε, Φ, hqea, hεpos, htype, u, hu, hφ, h1, h2, h3⟩

/-- **The positive-current root reduced to its two remaining inputs.**  Under the standing
hypotheses of `PositiveCurrentInputInterface.ct22Copy4_positiveCurrentInput` (`{θ}` big,
`0 < dim V < n`, `V ⊄ E_nn(α)`), the `u`-part of the trace package and `lem:domination` on `V`
give `PositiveCurrentInput`. -/
theorem positiveCurrentInput_of_traceUPart [CompactSpace X]
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) (hdim_pos : 0 < V.dim)
    (hdim_lt : V.dim < n)
    (hnonNef : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    (hU : TraceUPart omega θ V hV) (hdom : HasDominationLemma omega θ V hV) :
    PositiveCurrentInput omega θ V hV :=
  positiveCurrentInput_of_tracePackage_of_isBigClass omega θ hbig V hV hdim_pos hdim_lt
    (hasTracePackage_of_traceUPart (hdim_pos.trans hdim_lt) omega θ hbig V hV hnonNef hU) hdom

end UPart

end

end SGPT.Foundations.Analysis.Pending.PositiveCurrentAssembly

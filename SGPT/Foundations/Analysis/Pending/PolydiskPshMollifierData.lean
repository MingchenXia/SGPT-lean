import SGPT.Foundations.Analysis.Pending.PolydiskPerronDecreasingLimit
import SGPT.Foundations.Analysis.Pending.UniformBoundedGlobalMass

set_option autoImplicit false

/-!
# Balayage on the polydisk for a plurisubharmonic datum

`Pending.PolydiskPerronDecreasingLimit` proves the local form of Xia's
Lemma 2.4.3 for boundary data that are **decreasing limits of `C²` Perron
data**.  This module supplies such a sequence for the data the lemma is
actually applied to, and thereby discharges the hypothesis.

## Which data the lemma needs

In Xia's proof of Lemma 2.4.3 the balayage is performed on `P_θ(f)`, not on
`f`: *"let `φ ∈ PSH(X,θ)` be the balayage of `P_θ(f)` on `B`"*.  On
`U = {P_θ(f) < f} ∖ nK({θ})` the function `P_θ(f)` is `θ`-plurisubharmonic and
locally bounded, so in a holomorphic chart it is a **locally bounded
plurisubharmonic function on a neighbourhood of the closed polydisk**.  The same
is true of Proposition 1.2.9, whose balayage
`û = sup {v ∈ PSH(Ω) : v ≤ u off D}` takes a plurisubharmonic `u`.  A boundary
datum that is merely continuous never occurs.

That restriction is what makes the approximation elementary.  A general
continuous datum on the topological boundary `∂P` is *not* a decreasing limit of
`IsPerronData` when `n ≥ 2`, because `∂P` contains analytic discs along which
every member of the competitor class obeys the sub-mean-value inequality; a
plurisubharmonic datum obeys those inequalities already, so the obstruction is
vacuous for it.

## The construction

`HolomorphicPullback.exists_decreasingMollifierApproximation` mollifies: on any
`A` relatively compact in `Ω` it produces smooth plurisubharmonic `f j` on `A`,
antitone in `j`, converging to `u` pointwise **everywhere** on `A`.  Choosing
`A` between the compact `P̄` and `Ω` puts the whole closed polydisk — boundary
included — inside the region where all three properties hold.

One technical step remains: `IsPerronData` and the `C²` hypothesis are global
conditions on `ℂⁿ`, while `f j` is smooth only on `A`.  A test function `χ`
equal to `1` on a neighbourhood `W` of `P̄` and supported in `A` fixes this:
`χ · f j`, extended by zero, is globally smooth
(`UniformBoundedGlobalMass.contDiff_cutoff_extend`) and agrees with `f j` on
`W ⊇ P̄`, so it is plurisubharmonic on `P`, continuous on `P̄`, and has exactly
the boundary values of `f j`.

Source: M. Xia, *Sheaves and geometry of pluripotential theory*, Lemma 2.4.3
and Proposition 1.2.9; Z. Błocki, *The complex Monge--Ampère operator in
pluripotential theory*, §2.3.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-- **A locally bounded plurisubharmonic function near the closed polydisk is a
decreasing limit of `C²` Perron data.**  The approximants are its mollifications,
cut off outside a relatively compact neighbourhood of `P̄` so as to be globally
smooth; the cutoff is identically `1` near `P̄`, so it changes neither the
boundary values nor plurisubharmonicity on `P`. -/
theorem exists_isPerronData_contDiff_antitone_tendsto
    (hn : 0 < n) {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    (hPΩ : closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n))) :
    ∃ v : ℕ → ComplexModel n → ℝ,
      (∀ j, IsPerronData (v j)) ∧ (∀ j, ContDiff ℝ 2 (v j)) ∧
      (∀ z ∈ closedUnitPolydisk n, Antitone fun j ↦ v j z) ∧
      (∀ z ∈ closedUnitPolydisk n, Tendsto (fun j ↦ v j z) atTop (𝓝 (u z))) := by
  classical
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure
      (isCompact_closedUnitPolydisk (n := n)) Ω.isOpen hPΩ
  set A : Opens (ComplexModel n) := ⟨V, hVo⟩ with hAdef
  have hrc : RelativelyCompactIn A Ω := ⟨hVc, hVΩ⟩
  obtain ⟨f, hfsmooth, hfanti, hftend⟩ :=
    HolomorphicPullback.exists_decreasingMollifierApproximation hu hrc
  obtain ⟨χ, hχ1, -⟩ :=
    exists_testFunction_eq_one_nhds_compact (Ω := A) (K := closedUnitPolydisk n)
      isCompact_closedUnitPolydisk hKV
  obtain ⟨N, hNo, hKN, hχN⟩ := eventually_nhdsSet_iff_exists.mp hχ1
  set W : Set (ComplexModel n) := N ∩ V with hWdef
  have hWo : IsOpen W := hNo.inter hVo
  have hKW : closedUnitPolydisk n ⊆ W := fun z hz => ⟨hKN hz, hKV hz⟩
  set v : ℕ → ComplexModel n → ℝ :=
    fun j => V.indicator (fun z => (χ : ComplexModel n → ℝ) z * f j z) with hvdef
  have heq : ∀ j, ∀ z ∈ W, v j z = f j z := by
    intro j z hz
    rw [hvdef]
    simp only
    rw [Set.indicator_of_mem hz.2, hχN z hz.1, one_mul]
  have hsmooth : ∀ j, ContDiff ℝ ∞ (v j) := fun j =>
    UniformBoundedGlobalMass.contDiff_cutoff_extend (Ω := A) χ.contDiff
      χ.tsupport_subset (hfsmooth j).1
  have hC2 : ∀ j, ContDiff ℝ 2 (v j) := fun j => (hsmooth j).of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨v, fun j => ⟨hn, ((hsmooth j).continuous).continuousOn, ?_⟩, hC2, ?_, ?_⟩
  · intro z hz
    have hzP : z ∈ closedUnitPolydisk n := unitPolydisk_subset_closedUnitPolydisk hz
    have hzW : z ∈ W := hKW hzP
    refine ((hfsmooth j).2.1 z (hKV hzP)).congr ?_
    filter_upwards [hWo.mem_nhds hzW] with y hy
    rw [heq j y hy]
  · intro z hz
    have hzW : z ∈ W := hKW hz
    have := hfanti z (hKV hz)
    simpa only [heq _ z hzW] using this
  · intro z hz
    have hzW : z ∈ W := hKW hz
    have := hftend z (hKV hz)
    simpa only [heq _ z hzW] using this

/-- **Balayage on the polydisk for a plurisubharmonic datum.**  The
Perron--Bremermann envelope of a locally bounded plurisubharmonic function
defined near the closed polydisk carries no Bedford--Taylor mass inside the
polydisk: it solves the homogeneous Monge--Ampère equation there.

This is the local form of Xia's Lemma 2.4.3 for exactly the data the lemma
balayages. -/
theorem eq_zero_of_isBTLimit_perronEnvelope_of_isLocallyBoundedPshOn
    (hn : 0 < n) {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    (hPΩ : closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)))
    {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit (unitPolydiskOpens n) (fun _ ↦ perronEnvelope u) μ) :
    μ = 0 := by
  obtain ⟨v, hv, hv2, hanti, htend⟩ :=
    exists_isPerronData_contDiff_antitone_tendsto hn hu hPΩ
  obtain ⟨C, -, hC⟩ :=
    hu.exists_compact_abs_bound (isCompact_closedUnitPolydisk (n := n)) hPΩ
  exact eq_zero_of_isBTLimit_perronEnvelope_of_antitone hv hv2
    (fun ζ hζ => hanti ζ hζ.1) (fun ζ hζ => htend ζ hζ.1)
    (M := C) (fun x hx => (le_abs_self _).trans (hC x hx))
    (c := -C) (fun ζ hζ => neg_le_of_abs_le (hC ζ hζ.1)) hμ

/-- **The envelope of a plurisubharmonic datum is a locally bounded
plurisubharmonic function on the polydisk.**  It is the pointwise infimum of the
envelopes of the mollifications, and that infimum is handled by
`isLocallyBoundedPshOn_iInf_perronEnvelope`.  No continuity of `u` on `P̄` is
assumed, so `IsPerronData u` itself is unavailable. -/
theorem isLocallyBoundedPshOn_perronEnvelope_of_isLocallyBoundedPshOn
    (hn : 0 < n) {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    (hPΩ : closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n))) :
    IsLocallyBoundedPshOn (unitPolydiskOpens n) (perronEnvelope u) := by
  obtain ⟨v, hv, -, hanti, htend⟩ :=
    exists_isPerronData_contDiff_antitone_tendsto hn hu hPΩ
  obtain ⟨C, -, hC⟩ :=
    hu.exists_compact_abs_bound (isCompact_closedUnitPolydisk (n := n)) hPΩ
  have hcv : ∀ j, ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, -C ≤ v j ζ := fun j ζ hζ =>
    (neg_le_of_abs_le (hC ζ hζ.1)).trans ((hanti ζ hζ.1).le_of_tendsto (htend ζ hζ.1) j)
  have hiInf := isLocallyBoundedPshOn_iInf_perronEnvelope hv (fun ζ hζ => hanti ζ hζ.1) hcv
  have heq : ∀ y ∈ (unitPolydiskOpens n : Set (ComplexModel n)),
      (⨅ j, perronEnvelope (v j) y) = perronEnvelope u y := fun y hy =>
    (perronEnvelope_iInf_eq_of_antitone hv (fun ζ hζ => hanti ζ hζ.1)
      (fun ζ hζ => htend ζ hζ.1) (M := C) (fun x hx => (le_abs_self _).trans (hC x hx))
      (c := -C) (fun ζ hζ => neg_le_of_abs_le (hC ζ hζ.1)) hy).symm
  refine ⟨fun x hx => (hiInf.1 x hx).congr ?_, fun z hz => ?_⟩
  · filter_upwards [(unitPolydiskOpens n).isOpen.mem_nhds hx] with y hy
    rw [heq y hy]
  · obtain ⟨V', hzV', hVΩ', C', hC'⟩ := hiInf.2 z hz
    exact ⟨V', hzV', hVΩ', C', fun y hy => heq y (hVΩ' hy) ▸ hC' y hy⟩

/-- **The homogeneous Monge--Ampère equation for the balayage of a
plurisubharmonic datum**, in the project's usual vocabulary: the
Bedford--Taylor measure of the envelope on the open polydisk is the zero
measure. -/
theorem eq_zero_of_isLocalBedfordTaylorMeasure_perronEnvelope_of_isLocallyBoundedPshOn
    (hn : 0 < n) {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    (hPΩ : closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)))
    {μ : Measure (ComplexModel n)}
    (hμ : IsLocalBedfordTaylorMeasure (unitPolydiskOpens n) (perronEnvelope u) μ) :
    μ = 0 :=
  eq_zero_of_isBTLimit_perronEnvelope_of_isLocallyBoundedPshOn hn hu hPΩ (IsLocalBedfordTaylorMeasure.isBTLimit hμ)

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end

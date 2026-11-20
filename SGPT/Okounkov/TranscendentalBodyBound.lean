import SGPT.Okounkov.TranscendentalCoreDefs
import SGPT.Okounkov.PotentialFlagValuationIndependence
import SGPT.Okounkov.DivisorResidualGenericZero
import SGPT.Okounkov.GlobalDivisorResidual
import SGPT.Okounkov.FlattenedDivisorMetric
import SGPT.Trace.TraceEnvelope
import SGPT.Foundations.Analysis.Pending.UniformLelongBound
import SGPT.Foundations.Analysis.Pending.UniformPerturbedKahlerLowerBound
import SGPT.Foundations.Analysis.Pending.KahlerDomination

/-!
# Uniform bounds for flag valuations and compactness of Okounkov bodies

Source: blueprint node `tok:valuation-bound` (DRWNXZ §3, "bounded by cohomological constants",
citing Deng, *Transcendental Morse inequality and generalized Okounkov bodies*, Lemma 4.3), in
the following form: **for every closed real `(1,1)`-form `θ` there is a constant `C` such that
every coordinate of `ν_{Y•}(θ + dd^c φ)` lies in `[0, C]` for every `φ ∈ PSH(X, θ)`**, and the
constant serves all `θ + η` with `η ≤ ω`. Consequently `Δ_{Y•}(ξ)` is compact (blueprint
`tok:body-basic`).

## Route

The statement is proved for **all** quasi-psh potentials (not only those with analytic
singularities), by induction on the dimension along the recursion defining the valuation
(`OriginalPotentialFlagValuation`): with `θ ≤ A ω`,

* the first coordinate `ν₁` is the generic Lelong number of `φ` along `Y₁`, at most the
  Lelong number at a point of `Y₁`, hence at most the uniform Lelong bound `N_A` of all
  `Aω`-psh potentials (`UniformLelongBound.hasUniformLelongBound`; on a compact manifold the
  Lelong numbers of all `θ`-psh functions are bounded by one constant);
* for one **fixed** unit metric `E` of `Y₁` (`exists_normalized_smooth_divisor_metric_normal_forms`)
  the residual `φ - ν₁ log |s|²_E` is `(Aω - ν₁ {Y₁}_E)`-psh with generic Lelong number `0`, and
  it has a trace operator `τ` on `Y₁` lying in `PSH(Y₁, (Aω - ν₁ {Y₁}_E + ω)|_{Y₁})`
  (`SGPT.Trace.hasPositiveSourceTraceAlong_add_kahler`, the observation after the book's
  `def:traceop2`);
* `(Aω - ν₁ {Y₁}_E + ω)|_{Y₁} ≤ (A + 1 + N_A B) ω|_{Y₁}`, where `{Y₁}_E|_{Y₁} + B ω|_{Y₁} ≥ 0`
  (`KahlerDomination`), so `τ` is `A' ω|_{Y₁}`-psh with `A'` independent of `φ`;
* the remaining coordinates of `ν(φ)` are those of `ν(τ)` on the tail flag
  (`potentialFlagValuation_tail_of_originalFlagStep`, independence of every choice), bounded by
  the induction hypothesis for `A'`.

This avoids `tok:valuation-analytic` (the identification of traces with restrictions for
analytic singularities) and the cohomological mass computation of the blueprint proof: the
mass bound is replaced by the uniform Lelong bound, and the class of the restriction is
controlled through the trace in the class `(θ + ω)|_{Y₁}`.

## Main results

* `exists_potentialFlagValuation_le_of_smul_kahler`: the bound for `A ω`-psh potentials.
* `exists_flagValuation_le`: for every `θ` there is `C` with `ν_i(φ) ≤ C` for all
  `φ ∈ PSH(X, θ)`.
* `exists_flagValuation_le_uniform`: one `C` for all `φ ∈ PSH(X, θ + η)` with `η ≤ ω`
  (blueprint `tok:valuation-bound`).
* `tradOkounkovBody_subset_Icc`, `isCompact_tradOkounkovBody`: `Δ_{Y•}(ξ)` is compact.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalBody

open Set Filter
open scoped NNReal ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.NaturalSubmanifoldSourceTraceDefinition
open SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
open SGPT.Okounkov.TranscendentalCore

/-! ### Linearity of the pullback of closed forms -/

section Pullback

variable {k n : ℕ} {V M : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {f : V → M}

theorem pullback_add' (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a b : ClosedRealOneOneForm n M) :
    ClosedRealOneOneForm.pullback hf (a + b) =
      ClosedRealOneOneForm.pullback hf a + ClosedRealOneOneForm.pullback hf b := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

theorem pullback_smul' (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (t : ℝ) (a : ClosedRealOneOneForm n M) :
    ClosedRealOneOneForm.pullback hf (t • a) = t • ClosedRealOneOneForm.pullback hf a := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

theorem pullback_sub' (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a b : ClosedRealOneOneForm n M) :
    ClosedRealOneOneForm.pullback hf (a - b) =
      ClosedRealOneOneForm.pullback hf a - ClosedRealOneOneForm.pullback hf b := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

end Pullback

/-! ### The bound -/

/-- **Blueprint `tok:valuation-bound`, core form**: for every `A` there is `C` such that every
coordinate of `ν_{Y•}(φ)` is at most `C` for every `A ω`-psh potential `φ` (all quasi-psh
potentials, by induction on the dimension). -/
theorem exists_potentialFlagValuation_le_of_smul_kahler :
    ∀ (n : ℕ) (F : OriginalFlagGeometry.{u} n) (A : ℝ), ∃ C : ℝ,
      ∀ (v : F.carrier → EReal) (hv : IsThetaPshPotential (A • F.omega.form).val v)
        (i : Fin n), ((potentialFlagValuation F hv i : ℝ≥0) : ℝ) ≤ C := by
  intro n
  induction n with
  | zero =>
      intro F A
      exact ⟨0, fun v hv i => Fin.elim0 i⟩
  | succ m ih =>
      intro F A
      -- the uniform Lelong bound of all `A ω`-psh potentials
      obtain ⟨N, hN⟩ := UniformLelongBound.hasUniformLelongBound (Nat.succ_pos m)
        (A • F.omega.form)
      set N' : ℝ := max N 0 with hN'
      have hN'0 : 0 ≤ N' := le_max_right _ _
      -- one fixed unit metric of `Y₁`
      obtain ⟨D, hDI, E, hEW, hmetric, -⟩ :=
        exists_normalized_smooth_divisor_metric_normal_forms (M := F.carrier) F.firstDivisor
      let W := F.flag (1 : Fin (m + 2))
      let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) F.firstDivisor.2.2
      let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
        (Nat.le_succ m) F.firstDivisor.2.2
      let : CompactSpace W := F.tail.compact
      let : ConnectedSpace W := F.tail.connected
      let : MeasurableSpace W := borel W
      have : BorelSpace W := ⟨rfl⟩
      let hι := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) F.firstDivisor.2.2
      let ωW : KahlerBackground m W :=
        SubmanifoldKahlerRestriction.kahlerBackground (Nat.le_succ m) F.firstDivisor.2.2 F.omega
      have hωW : ωW.form = ClosedRealOneOneForm.pullback hι F.omega.form := rfl
      -- the curvature of `E` restricted to `Y₁` is bounded below by `-B ω|_{Y₁}`
      obtain ⟨B, hB, hBsemi⟩ :=
        KahlerDomination.exists_pos_isSemipositive_add_smul ωW
          (ClosedRealOneOneForm.pullback hι E.curvature)
      set A' : ℝ := A + 1 + N' * B with hA'
      obtain ⟨C', hC'⟩ := ih F.tail A'
      refine ⟨max N' C', fun v hv i => ?_⟩
      -- the first coordinate
      have hfirst : ((potentialFlagValuation F hv 0 : ℝ≥0) : ℝ) ≤ N' := by
        have h := potentialFlagValuation_first F hv
        obtain ⟨y₀, hy₀⟩ := F.firstDivisor.2.1.nonempty
        have hle : sourceGenericLelongNumber (n := m + 1)
            (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) v ≤
            squaredLogLelongNumber (n := m + 1) v y₀ :=
          iInf_le (fun y : F.flag (1 : Fin (m + 2)) =>
            squaredLogLelongNumber (n := m + 1) v (y : F.carrier)) ⟨y₀, hy₀⟩
        have hsq : squaredLogLelongNumber (n := m + 1) v y₀ ≤ lelongNumber (n := m + 1) v y₀ := by
          rw [lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)]
          calc squaredLogLelongNumber (n := m + 1) v y₀
              = 1 * squaredLogLelongNumber (n := m + 1) v y₀ := (one_mul _).symm
            _ ≤ 2 * squaredLogLelongNumber (n := m + 1) v y₀ := by gcongr; norm_num
        have hlel := hN v hv y₀
        have hall : (potentialFlagValuation F hv 0 : ℝ≥0∞) ≤ ENNReal.ofReal N' := by
          rw [h]
          exact hle.trans (hsq.trans (hlel.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))))
        have hfin : ENNReal.ofReal N' ≠ ⊤ := ENNReal.ofReal_ne_top
        have := (ENNReal.toReal_le_toReal ENNReal.coe_ne_top hfin).mpr hall
        simpa [ENNReal.toReal_ofReal hN'0] using this
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hfirst.trans (le_max_left _ _)
      · -- the residual along `Y₁` with the fixed metric `E`
        set c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1)
          (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) v).toNNReal with hc
        have hcN : (c : ℝ) ≤ N' := by
          have h0 := potentialFlagValuation_first F hv
          have hc' : (potentialFlagValuation F hv 0 : ℝ≥0) = c := by
            rw [hc, ← h0, ENNReal.toNNReal_coe]
          rw [← hc']
          exact hfirst
        have hr := isThetaPshPotential_smooth_divisor_residual_of_unit_metric hv F.firstDivisor
          D hDI E hEW hmetric
        have hgen := sourceGeneric_smooth_divisor_residual_eq_zero hv F.firstDivisor
          D hDI E hEW hmetric hr
        -- a trace operator in the class `(A ω - c {Y₁} + ω)|_{Y₁}`
        have hpull : (ClosedRealOneOneForm.pullback hι F.omega.form).val.IsKahler := by
          rw [← hωW]
          exact ωW.isKahler
        obtain ⟨τ, htrace, hτ, -⟩ := SGPT.Trace.hasPositiveSourceTraceAlong_add_kahler
          (Nat.le_succ m) F.omega F.omega ωW hι hpull hr hgen
        have hstep : OriginalFlagStep F v τ :=
          ⟨A • F.omega.form, hv, D, hDI, E, hEW, hmetric, htrace⟩
        -- `τ` is `A' ω|_{Y₁}`-psh
        have hsemi : (A' • ωW.form - ClosedRealOneOneForm.pullback hι
            ((A • F.omega.form - (c : ℝ) • E.curvature) + F.omega.form)).val.IsSemipositive := by
          have heq : A' • ωW.form - ClosedRealOneOneForm.pullback hι
              ((A • F.omega.form - (c : ℝ) • E.curvature) + F.omega.form) =
              ((N' - c) * B) • ωW.form +
                (c : ℝ) • (ClosedRealOneOneForm.pullback hι E.curvature + B • ωW.form) := by
            rw [pullback_add', pullback_sub', pullback_smul', pullback_smul', ← hωW, hA']
            module
          rw [heq]
          refine UniformPerturbedKahlerLowerBound.isSemipositive_add
            (KahlerDomination.isSemipositive_smul ωW.isSemipositive ?_)
            (KahlerDomination.isSemipositive_smul hBsemi (NNReal.coe_nonneg c))
          exact mul_nonneg (by linarith) hB.le
        have hτ' : IsThetaPshPotential (A' • F.tail.omega.form).val τ := by
          have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hτ hsemi
          rw [add_sub_cancel] at h
          exact h
        have htail := potentialFlagValuation_tail_of_originalFlagStep F hv hstep hτ'
        have hj := congrFun htail j
        change ((potentialFlagValuation F hv j.succ : ℝ≥0) : ℝ) ≤ max N' C'
        rw [hj]
        exact (hC' τ hτ' j).trans (le_max_right _ _)

variable {n : ℕ} {F : OriginalFlagGeometry.{u} n}

/-- **Blueprint `tok:valuation-bound`**: for every closed real `(1,1)`-form `θ` there is a
constant `C` such that every coordinate of `ν_{Y•}(θ + dd^c φ)` lies in `[0, C]` for every
`φ ∈ PSH(X, θ)`. -/
theorem exists_flagValuation_le (θ : ClosedRealOneOneForm n F.carrier) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : F.carrier → EReal, IsThetaPshPotential θ.val φ →
      ∀ i, flagValuation F φ i ≤ C := by
  obtain ⟨A, -, hA⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul F.omega (-θ)
  obtain ⟨C, hC⟩ := exists_potentialFlagValuation_le_of_smul_kahler n F A
  refine ⟨max C 0, le_max_right _ _, fun φ hφ i => ?_⟩
  have hφA : IsThetaPshPotential (A • F.omega.form).val φ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hφ hA
    have heq : θ + (-θ + A • F.omega.form) = A • F.omega.form := by abel
    rw [heq] at h
    exact h
  rw [flagValuation_eq hφA]
  exact (hC φ hφA i).trans (le_max_left _ _)

/-- **Blueprint `tok:valuation-bound`, uniform form**: for every `θ` there is `C` such that for
every closed real `(1,1)`-form `η ≤ ω` and every `φ ∈ PSH(X, θ + η)`, all coordinates of
`ν_{Y•}(φ)` lie in `[0, C]`. -/
theorem exists_flagValuation_le_uniform (θ : ClosedRealOneOneForm n F.carrier) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ClosedRealOneOneForm n F.carrier,
      (F.omega.form - η).val.IsSemipositive →
      ∀ φ : F.carrier → EReal, IsThetaPshPotential (θ + η).val φ →
        ∀ i, flagValuation F φ i ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_flagValuation_le (F := F) (θ + F.omega.form)
  refine ⟨C, hC0, fun η hη φ hφ i => hC φ ?_ i⟩
  have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hφ hη
  have heq : θ + η + (F.omega.form - η) = θ + F.omega.form := by abel
  rw [heq] at h
  exact h

/-- `Δ_{Y•}(ξ)` lies in a cube `[0, C]ⁿ`. -/
theorem exists_tradOkounkovBody_subset_Icc (θ : ClosedRealOneOneForm n F.carrier) :
    ∃ C : ℝ, 0 ≤ C ∧ tradOkounkovBody F θ ⊆ Icc (0 : Fin n → ℝ) (fun _ => C) := by
  obtain ⟨C, hC0, hC⟩ := exists_flagValuation_le (F := F) θ
  refine ⟨C, hC0, ?_⟩
  rw [tradOkounkovBody_eq_closure_image]
  refine closure_minimal ?_ isClosed_Icc
  rintro _ ⟨φ, hφ, rfl⟩
  exact ⟨fun i => flagValuation_nonneg φ i,
    fun i => hC φ (isThetaPshPotential_of_mem_gentleCurrents hφ) i⟩

/-- `Δ_{Y•}(ξ)` is bounded. -/
theorem isBounded_tradOkounkovBody (θ : ClosedRealOneOneForm n F.carrier) :
    Bornology.IsBounded (tradOkounkovBody F θ) := by
  obtain ⟨C, -, hsub⟩ := exists_tradOkounkovBody_subset_Icc (F := F) θ
  exact isCompact_Icc.isBounded.subset hsub

/-- **Blueprint `tok:body-basic`, compactness**: `Δ_{Y•}(ξ)` is compact. -/
theorem isCompact_tradOkounkovBody (θ : ClosedRealOneOneForm n F.carrier) :
    IsCompact (tradOkounkovBody F θ) := by
  obtain ⟨C, -, hsub⟩ := exists_tradOkounkovBody_subset_Icc (F := F) θ
  exact isCompact_Icc.of_isClosed_subset (isClosed_tradOkounkovBody θ) hsub

end SGPT.Okounkov.TranscendentalBody

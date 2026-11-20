import SGPT.Foundations.Analysis.Pending.LinearProjectionJacobian
import SGPT.Foundations.Analysis.Pending.PluckerSpanningBound
import SGPT.Foundations.Analysis.Pending.MultiplicityAreaBound

set_option autoImplicit false

/-!
# Demailly's own assembly of CADG III.2.6, against a decomposable basis

`Pending.FlatVolumeFibreBound` assembles the local finite-volume theorem from the
`binom n k` COORDINATE projections of one chart, because `Pending.CauchyBinet`
expands the flat density over the coordinate `k`-subsets.  Demailly does not:
he expands against an ARBITRARY basis of `Λ^{k,k}` made of decomposable forms
and then perturbs each basis form separately, so that the projection attached to
one basis form becomes a ramified covering while the family remains a basis.

This module is that assembly, with the geometric input left as hypotheses:

  `flatPatchDensity` `=` `k!·Re det (LᴴL)`
      (`Pending.FlatDensityGramDeterminant`),
  `Re det (LᴴL) ≤ C · Σ_s ‖det (B_s·L)‖²` for a Plücker-spanning family `B`
      (`Pending.PluckerSpanningBound.exists_gram_le`),
  `‖det (B_s·L)‖²` `=` the real Jacobian of `B_s ∘ e ∘ γ`
      (`Pending.LinearProjectionJacobian.det_linearProjectedDerivative`),
  and a family of finite-to-one maps into `Δ` integrates its Jacobian to at most
  the sheet number times `vol Δ`
      (`Pending.MultiplicityAreaBound`).

The constant `C` depends only on the family `B` — not on the regular-piece
family, the point, or the neighbourhood — so `exists_flatVolumeConst` produces it
once and for all before any geometry is fixed.  The remaining hypotheses `hmaps`
and `hfib` are exactly Demailly's "each `π_s` defines a ramified covering of
`A ∩ (Δ'×Δ'')`", in the almost-everywhere form that the area bound consumes.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal Matrix

namespace SGPT.Foundations.Analysis.Pending.DecomposableBasisFlatVolume

open FirstPass FirstPass.NumericalRestrictedVolume FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.FlatPatchDensityComparison
  SGPT.Foundations.Analysis.Pending.CauchyBinet
  SGPT.Foundations.Analysis.Pending.FlatDensityGramDeterminant
  SGPT.Foundations.Analysis.Pending.LinearProjectionJacobian
  SGPT.Foundations.Analysis.Pending.PluckerSpanningBound
  SGPT.Foundations.Analysis.Pending.MultiplicityAreaBound

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- **The whole estimate, granted one Plücker-spanning family of projections and
its sheet numbers.**  For a family `B` of `ℂ`-linear maps `ℂⁿ → ℂ^k` whose
Plücker functionals separate points there is a constant `C` — depending on `B`
alone — such that every regular-piece family seen by the chart `e`, all of whose
`B_s`-projections land in `Δ` with at most `N` preimages over almost every point
of `Δ`, has total flat parameter mass at most `C·N·vol Δ`. -/
theorem exists_flatVolumeConst {σ : Type*} [Fintype σ]
    (B : σ → (ComplexModel n →L[ℂ] ComplexModel V.dim))
    (hspan : SpansPlucker (fun s => rectMatrix (B s))) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (e : ComplexChart n M) (F : RegularPieceFamily V (∅ : Set M)),
        (∀ i, F.piece i ⊆ chartDomain e (F.patch i)) →
        ∀ {Δ : Set (ComplexModel V.dim)}, MeasurableSet Δ →
        ∀ {N : ℕ},
          (∀ (s : σ) (i : Fin F.size),
            MapsTo (linearProjectedParametrization (B s) e (F.patch i)) (F.piece i) Δ) →
          (∀ s : σ, ∀ᵐ y : ComplexModel V.dim, y ∈ Δ →
            ∑ i, (F.piece i ∩
              linearProjectedParametrization (B s) e (F.patch i) ⁻¹' {y}).encard
                ≤ (N : ℕ∞)) →
          ∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (flatPatchDensity e (F.patch i) w) ≤
            C * (N : ℝ≥0∞) * volume Δ := by
  classical
  obtain ⟨C, hC0, hCbound⟩ := exists_gram_le (fun s => rectMatrix (B s)) hspan
  refine ⟨(V.dim.factorial : ℝ≥0∞) * ENNReal.ofReal C * (Fintype.card σ : ℝ≥0∞),
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) (by simp), ?_⟩
  intro e F hchart Δ hΔ N hmaps hfib
  set c : ℝ≥0∞ := (V.dim.factorial : ℝ≥0∞) * ENNReal.ofReal C with hc
  have hcne : c ≠ ⊤ := ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hstrict : ∀ (s : σ) (i : Fin F.size), ∀ w ∈ F.piece i,
      HasStrictFDerivAt (linearProjectedParametrization (B s) e (F.patch i))
        (linearProjectedDerivative (B s) e (F.patch i) w) w :=
    fun s i w hw => hasStrictFDerivAt_linearProjectedParametrization (B s) (hchart i hw)
  have hae : ∀ (s : σ) (i : Fin F.size),
      AEMeasurable
        (fun w => ENNReal.ofReal |(linearProjectedDerivative (B s) e (F.patch i) w).det|)
        (volume.restrict (F.piece i)) :=
    fun s i => aemeasurable_ofReal_abs_det_fderivWithin volume (F.measurableSet_piece i)
      (fun w hw => (hstrict s i w hw).hasFDerivAt.hasFDerivWithinAt)
  -- The pointwise estimate: the flat density is at most `c` times the sum of the
  -- real Jacobians of the `m` projections.
  have hpt : ∀ (i : Fin F.size), ∀ w ∈ F.piece i,
      ENNReal.ofReal (flatPatchDensity e (F.patch i) w) ≤
        c * ∑ s : σ,
          ENNReal.ofReal |(linearProjectedDerivative (B s) e (F.patch i) w).det| := by
    intro i w hw
    set L := chartPullbackDerivative e (F.patch i) w with hL
    have hgram : flatPatchDensity e (F.patch i) w =
        (V.dim.factorial : ℝ) * ((rectGram L).det).re :=
      flatPatchDensity_eq_gram e (F.patch i) (hchart i hw)
    have hbound : ((rectGram L).det).re ≤
        C * ∑ s : σ, ‖(rectMatrix (B s) * standardRectMatrix L).det‖ ^ 2 := by
      rw [rectGram_eq]
      exact hCbound (standardRectMatrix L)
    have hjac : ∀ s : σ,
        ‖(rectMatrix (B s) * standardRectMatrix L).det‖ ^ 2 =
          |(linearProjectedDerivative (B s) e (F.patch i) w).det| := by
      intro s
      rw [det_linearProjectedDerivative (B s) (hchart i hw), abs_of_nonneg (by positivity)]
    have hle : flatPatchDensity e (F.patch i) w ≤
        ((V.dim.factorial : ℝ) * C) * ∑ s : σ,
          |(linearProjectedDerivative (B s) e (F.patch i) w).det| := by
      rw [hgram, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine hbound.trans (le_of_eq ?_)
      exact congrArg _ (Finset.sum_congr rfl fun s _ => hjac s)
    calc ENNReal.ofReal (flatPatchDensity e (F.patch i) w)
        ≤ ENNReal.ofReal (((V.dim.factorial : ℝ) * C) * ∑ s : σ,
            |(linearProjectedDerivative (B s) e (F.patch i) w).det|) :=
          ENNReal.ofReal_le_ofReal hle
      _ = c * ∑ s : σ,
            ENNReal.ofReal |(linearProjectedDerivative (B s) e (F.patch i) w).det| := by
          rw [ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_sum_of_nonneg (fun s _ => abs_nonneg _), hc,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  have hstep : ∀ i, ∫⁻ w in F.piece i, ENNReal.ofReal (flatPatchDensity e (F.patch i) w) ≤
      c * ∑ s : σ,
        ∫⁻ w in F.piece i,
          ENNReal.ofReal |(linearProjectedDerivative (B s) e (F.patch i) w).det| := by
    intro i
    calc ∫⁻ w in F.piece i, ENNReal.ofReal (flatPatchDensity e (F.patch i) w)
        ≤ ∫⁻ w in F.piece i, c * ∑ s : σ,
            ENNReal.ofReal |(linearProjectedDerivative (B s) e (F.patch i) w).det| := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem (F.measurableSet_piece i)] with w hw
          exact hpt i w hw
      _ = c * ∑ s : σ, ∫⁻ w in F.piece i,
            ENNReal.ofReal |(linearProjectedDerivative (B s) e (F.patch i) w).det| := by
          rw [lintegral_const_mul' _ _ hcne]
          exact congrArg _ (lintegral_finsetSum' _ fun s _ => hae s i)
  have hperS : ∀ s : σ,
      ∑ i, ∫⁻ w in F.piece i,
          ENNReal.ofReal |(linearProjectedDerivative (B s) e (F.patch i) w).det| ≤
        (N : ℝ≥0∞) * volume Δ :=
    fun s => sum_lintegral_abs_det_le volume (S := fun i => F.piece i)
      (f := fun i => linearProjectedParametrization (B s) e (F.patch i))
      (f' := fun i w => linearProjectedDerivative (B s) e (F.patch i) w)
      (fun i => F.measurableSet_piece i) (fun i => hstrict s i) hΔ (fun i => hmaps s i)
      (hfib s)
  calc ∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (flatPatchDensity e (F.patch i) w)
      ≤ ∑ _i : Fin F.size, c * ∑ s : σ, ∫⁻ w in F.piece _i,
          ENNReal.ofReal |(linearProjectedDerivative (B s) e (F.patch _i) w).det| :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = c * ∑ s : σ, ∑ i, ∫⁻ w in F.piece i,
          ENNReal.ofReal |(linearProjectedDerivative (B s) e (F.patch i) w).det| := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ c * ∑ _s : σ, (N : ℝ≥0∞) * volume Δ := by
        gcongr with s _
        exact hperS s
    _ = (V.dim.factorial : ℝ≥0∞) * ENNReal.ofReal C * (Fintype.card σ : ℝ≥0∞) * (N : ℝ≥0∞) *
          volume Δ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
        ring

end SGPT.Foundations.Analysis.Pending.DecomposableBasisFlatVolume

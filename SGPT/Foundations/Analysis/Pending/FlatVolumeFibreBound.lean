import SGPT.Foundations.Analysis.Pending.ProjectedPatchJacobian
import SGPT.Foundations.Analysis.Pending.FlatDensityMinorExpansion
import SGPT.Foundations.Analysis.Pending.MultiplicityAreaBound

set_option autoImplicit false

/-!
# The local flat volume bound, granted the sheet numbers

This module assembles Demailly's proof of the local finite-volume theorem
(CADG III.2.6) from its analytic ingredients, leaving exactly one GEOMETRIC
hypothesis: a bound on the number of preimages of a point under each of the
`binom n k` coordinate projections.

  `flatPatchDensity` `=` `k!` times the sum of the squared `I`-minors
      (`Pending.FlatDensityMinorExpansion`, i.e. Cauchy--Binet),
  each squared minor `=` the real Jacobian of `π_I ∘ e ∘ γ`
      (`Pending.ProjectedPatchJacobian`),
  and a family of finite-to-one maps into `Δ` integrates its Jacobian to at most
  the sheet number times `vol Δ`
      (`Pending.MultiplicityAreaBound`).

`sum_lintegral_flatPatchDensity_le` is the conclusion.  Its hypotheses `hmaps`
and `hfib` are the only thing separating this project from
`Pending.LocalFlatVolumeBound.exists_localFlatVolumeBound`: one has to produce,
around a point of `V`, a neighbourhood `U` and a polydisc `Δ` such that every
coordinate projection maps the part of `V` in `U` into `Δ` with at most `N`
preimages over almost every point.  That is the branched-covering half of the
parametrization theorem, whose exact fibre count off the discriminant is already
in this project as `Pending.GermParametrizationData.SetsData.ncard_fibre`.  No
analysis and no measure theory is left in it.  For a FIXED chart those hypotheses
can still fail, and `Pending.GenericProjectionFlatBound` supplies the linear change
of coordinates that repairs them.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal Matrix

namespace SGPT.Foundations.Analysis.Pending.FlatVolumeFibreBound

open FirstPass FirstPass.NumericalRestrictedVolume FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.FlatPatchDensityComparison
  SGPT.Foundations.Analysis.Pending.CauchyBinet
  SGPT.Foundations.Analysis.Pending.ProjectedPatchJacobian
  SGPT.Foundations.Analysis.Pending.FlatDensityMinorExpansion
  SGPT.Foundations.Analysis.Pending.MultiplicityAreaBound

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The number of `k`-element sets of coordinates. -/
theorem card_cardSubset (k : ℕ) :
    Fintype.card (CardSubset k n) = n.choose k := by
  simp [Fintype.card_finset_len (α := Fin n) k]

/-- **The flat parameter mass of a regular-piece family, bounded by the sheet
numbers of the coordinate projections.**  If every piece is seen by the chart
`e`, every projection `π_I ∘ e ∘ γ` sends it into `Δ`, and over almost every point
of `Δ` the whole family has at most `N` preimages, then the total flat parameter
mass is at most `k! · binom n k · N · vol Δ`. -/
theorem sum_lintegral_flatPatchDensity_le
    (e : ComplexChart n M) (F : RegularPieceFamily V (∅ : Set M))
    (hchart : ∀ i, F.piece i ⊆ chartDomain e (F.patch i))
    {Δ : Set (ComplexModel V.dim)} (hΔ : MeasurableSet Δ) {N : ℕ}
    (hmaps : ∀ (I : CardSubset V.dim n) (i : Fin F.size),
      MapsTo (projectedParametrization I e (F.patch i)) (F.piece i) Δ)
    (hfib : ∀ I : CardSubset V.dim n, ∀ᵐ y,
      y ∈ Δ →
        ∑ i, (F.piece i ∩ projectedParametrization I e (F.patch i) ⁻¹' {y}).encard
          ≤ (N : ℕ∞)) :
    ∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (flatPatchDensity e (F.patch i) w) ≤
      (V.dim.factorial : ℝ≥0∞) * ((n.choose V.dim : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞) * volume Δ := by
  classical
  have hstrict : ∀ (I : CardSubset V.dim n) (i : Fin F.size), ∀ w ∈ F.piece i,
      HasStrictFDerivAt (projectedParametrization I e (F.patch i))
        (projectedDerivative I e (F.patch i) w) w :=
    fun I i w hw => hasStrictFDerivAt_projectedParametrization I (hchart i hw)
  have hae : ∀ (I : CardSubset V.dim n) (i : Fin F.size),
      AEMeasurable (fun w => ENNReal.ofReal |(projectedDerivative I e (F.patch i) w).det|)
        (volume.restrict (F.piece i)) :=
    fun I i => aemeasurable_ofReal_abs_det_fderivWithin volume (F.measurableSet_piece i)
      (fun w hw => (hstrict I i w hw).hasFDerivAt.hasFDerivWithinAt)
  have hpt : ∀ (i : Fin F.size), ∀ w ∈ F.piece i,
      ENNReal.ofReal (flatPatchDensity e (F.patch i) w) =
        (V.dim.factorial : ℝ≥0∞) * ∑ I : CardSubset V.dim n,
          ENNReal.ofReal |(projectedDerivative I e (F.patch i) w).det| := by
    intro i w hw
    rw [flatPatchDensity_eq_sum_minors e (F.patch i) (hchart i hw),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_sum_of_nonneg (fun I _ => by positivity)]
    refine congrArg _ (Finset.sum_congr rfl fun I _ => congrArg ENNReal.ofReal ?_)
    rw [det_projectedDerivative I (hchart i hw)]
    exact (abs_of_nonneg (by positivity)).symm
  have hstep : ∀ i, ∫⁻ w in F.piece i, ENNReal.ofReal (flatPatchDensity e (F.patch i) w) =
      (V.dim.factorial : ℝ≥0∞) * ∑ I : CardSubset V.dim n,
        ∫⁻ w in F.piece i, ENNReal.ofReal |(projectedDerivative I e (F.patch i) w).det| := by
    intro i
    rw [setLIntegral_congr_fun (F.measurableSet_piece i) (hpt i),
      lintegral_const_mul' _ _ (by simp)]
    exact congrArg _ (lintegral_finsetSum' _ fun I _ => hae I i)
  have hperI : ∀ I : CardSubset V.dim n,
      ∑ i, ∫⁻ w in F.piece i,
          ENNReal.ofReal |(projectedDerivative I e (F.patch i) w).det| ≤
        (N : ℝ≥0∞) * volume Δ :=
    fun I => sum_lintegral_abs_det_le volume (S := fun i => F.piece i)
      (f := fun i => projectedParametrization I e (F.patch i))
      (f' := fun i w => projectedDerivative I e (F.patch i) w)
      (fun i => F.measurableSet_piece i) (fun i => hstrict I i) hΔ (fun i => hmaps I i)
      (hfib I)
  calc ∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (flatPatchDensity e (F.patch i) w)
      = (V.dim.factorial : ℝ≥0∞) * ∑ I : CardSubset V.dim n, ∑ i,
          ∫⁻ w in F.piece i,
            ENNReal.ofReal |(projectedDerivative I e (F.patch i) w).det| := by
        rw [Finset.mul_sum]
        rw [Finset.sum_congr rfl fun i _ => hstep i, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_comm]
    _ ≤ (V.dim.factorial : ℝ≥0∞) * ∑ _I : CardSubset V.dim n, (N : ℝ≥0∞) * volume Δ := by
        gcongr with I _
        exact hperI I
    _ = (V.dim.factorial : ℝ≥0∞) * ((n.choose V.dim : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞) * volume Δ := by
        rw [Finset.sum_const, Finset.card_univ, card_cardSubset, nsmul_eq_mul]
        ring

end SGPT.Foundations.Analysis.Pending.FlatVolumeFibreBound

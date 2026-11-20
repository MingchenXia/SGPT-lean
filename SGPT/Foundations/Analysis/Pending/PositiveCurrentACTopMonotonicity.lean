import SGPT.Foundations.Analysis.Pending.ActualPositiveCurrentLebesgueACAddition
import SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACTopMeasure
import SGPT.Foundations.Analysis.Pending.MinkowskiDeterminant

set_option autoImplicit false

/-!
# Positive addition increases the actual AC top measure

The full blueprint proof precedes this source. The entire AC coefficient
part adds, its canonical density form adds almost everywhere, and determinant
monotonicity supplies the entire local and global measure inequalities.
No closedness, analytic type or finite determinant mass is required.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions
namespace SGPT.Foundations.Analysis.Pending.PositiveCurrentACTopMonotonicity

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalCurrentLebesgue LocalCurrentDeterminant LocalCurrentDensityMatrix
  ActualPositiveCurrentLebesgueUniqueness ActualPositiveCurrentLebesgueACAddition
  PositiveCurrentACTopMeasure GlobalPositiveCurrentACTopMeasure
  GlobalPositiveCurrentACRestriction GlobalCurrents GlobalCurrentPotentials
  ActualAnalyticCurrentLocalDensity TopDegreeDensity
attribute [local instance] addCommGroupFormSpan

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

private theorem acPart_add {S T : LocalProductCurrent (m + 1) U m}
    (hS : IsPositive S) (hT : IsPositive T) :
    acPart (hS.add hT) = acPart hS + acPart hT := by
  obtain ⟨_, hSs, _, hSa⟩ := part_trace_classes hS
  obtain ⟨_, hTs, _, hTa⟩ := part_trace_classes hT
  let hsg := (isPositive_sgPart hS).add (isPositive_sgPart hT)
  let hac := (isPositive_acPart hS).add (isPositive_acPart hT)
  have hsgs : hsg.traceMeasure ⟂ₘ volume := by
    rw [traceMeasure_add (isPositive_sgPart hS) (isPositive_sgPart hT)]
    exact hSs.add_left hTs
  have haca : hac.traceMeasure ≪ volume := by
    rw [traceMeasure_add (isPositive_acPart hS) (isPositive_acPart hT)]
    intro E hE
    rw [Measure.add_apply, hSa hE, hTa hE, add_zero]
  have hp := (parts_of_singular_add_absolutelyContinuous hsg hac hsgs haca).2
  have heq : (sgPart hS + sgPart hT) + (acPart hS + acPart hT) = S + T := by
    calc _ = (sgPart hS + acPart hS) + (sgPart hT + acPart hT) := by abel
      _ = S + T := by rw [sgPart_add_acPart, sgPart_add_acPart]
  simpa only [heq] using hp

/-- The canonical real AC two-form of a positive sum is the sum of the
canonical two-forms, on one genuine conull subset of its open domain. -/
theorem ae_acForm_add {S T : LocalProductCurrent (m + 1) U m}
    (hS : IsPositive S) (hT : IsPositive T) :
    ∀ᵐ x ∂(volume : Measure (ComplexModel (m + 1))), x ∈ U →
      acForm (hS.add hT) x = acForm hS x + acForm hT x := by
  classical
  have hγ (γ : formSpan (m + 1) m) :
      ∀ᵐ x ∂(volume : Measure (ComplexModel (m + 1))), x ∈ U →
        acWeight (hS.add hT) x * densityForm (hS.add hT) x γ =
          acWeight hS x * densityForm hS x γ + acWeight hT x * densityForm hT x γ := by
    let f : ComplexModel (m + 1) → ℝ := fun x =>
      acWeight (hS.add hT) x * densityForm (hS.add hT) x γ
    let g : ComplexModel (m + 1) → ℝ := fun x =>
      acWeight hS x * densityForm hS x γ + acWeight hT x * densityForm hT x γ
    have hf : LocallyIntegrableOn f U volume := locallyIntegrableOn_acDensity (hS.add hT) γ
    have hg : LocallyIntegrableOn g U volume :=
      (locallyIntegrableOn_acDensity hS γ).add (locallyIntegrableOn_acDensity hT γ)
    have hp (χ : 𝓓(U, ℝ)) : ∫ x, χ x * f x = ∫ x, χ x * g x := by
      have h := congrArg (fun C : LocalProductCurrent (m + 1) U m => C γ χ)
        (acPart_add hS hT)
      have hSi : Integrable (fun x => χ x * (acWeight hS x * densityForm hS x γ)) volume := by
        simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
          χ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) (locallyIntegrableOn_acDensity hS γ)
      have hTi : Integrable (fun x => χ x * (acWeight hT x * densityForm hT x γ)) volume := by
        simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
          χ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) (locallyIntegrableOn_acDensity hT γ)
      simpa only [acPart_apply, LinearMap.add_apply, _root_.add_apply, f, g,
        mul_add, integral_add hSi hTi] using h
    have hz := U.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.sub hg)
      (μ := volume) (fun ψ hψ hc hs => by
        let χ : 𝓓(U, ℝ) := ⟨ψ, hψ, hc, hs⟩
        have hif : Integrable (fun x => χ x * f x) volume := by
          simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
            χ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hf
        have hig : Integrable (fun x => χ x * g x) volume := by
          simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
            χ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hg
        change (∫ x, χ x * (f x - g x)) = 0
        simp only [mul_sub]
        rw [integral_sub hif hig, hp χ, sub_self])
    filter_upwards [hz] with x hx hxU
    exact sub_eq_zero.mp (hx hxU)
  have hb := ae_all_iff.mpr (fun i => hγ (formBasis (m + 1) m i))
  filter_upwards [hb] with x hx hxU
  have hL : (acWeight (hS.add hT) x) • densityForm (hS.add hT) x =
      (acWeight hS x) • densityForm hS x + (acWeight hT x) • densityForm hT x := by
    apply (formBasis (m + 1) m).ext
    intro i
    exact hx i hxU
  apply acForm_eq_of_forall (hS.add hT) x
    (LocalCurrentDensityMatrix.isOneOne_add (isOneOne_acForm hS x) (isOneOne_acForm hT x))
  intro γ
  have h := DFunLike.congr_fun hL γ
  change acWeight (hS.add hT) x * densityForm (hS.add hT) x γ =
    acWeight hS x * densityForm hS x γ + acWeight hT x * densityForm hT x γ at h
  rw [h, acWeight_mul_densityForm_eq, acWeight_mul_densityForm_eq,
    coordinateWedge_add_right, topDensity_add]

private theorem topDensity_eq_det {S : LocalProductCurrent (m + 1) U m}
    (hS : IsPositive S) (x : ComplexModel (m + 1)) :
    actualTopPowerDensity (acForm hS x) =
      ((m + 1).factorial : ℝ) / Real.pi ^ (m + 1) * (acMatrix hS x).det.re := by
  rw [actualTopPowerDensity_eq_normalizedTopPowerDensity _ (isOneOne_acForm hS x),
    normalizedTopPowerDensity, complexTopCoefficient_eq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

/-- The entire local canonical AC top measure increases under arbitrary
positive addition, with no closedness or finite-mass premise. -/
theorem acTopMeasure_le_add {S T : LocalProductCurrent (m + 1) U m}
    (hS : IsPositive S) (hT : IsPositive T) :
    acTopMeasure hS ≤ acTopMeasure (hS.add hT) := by
  unfold acTopMeasure
  rw [restrict_withDensity U.isOpen.measurableSet, restrict_withDensity U.isOpen.measurableSet]
  apply withDensity_mono
  filter_upwards [(ae_restrict_iff' U.isOpen.measurableSet).mpr (ae_acForm_add hS hT),
    ae_restrict_of_ae (ae_posSemidef_acMatrix hS),
    ae_restrict_of_ae (ae_posSemidef_acMatrix hT)] with x hx hxS hxT
  apply ENNReal.ofReal_le_ofReal
  rw [topDensity_eq_det, topDensity_eq_det]
  have heq : acMatrix (hS.add hT) x = acMatrix hS x + acMatrix hT x := by
    change normalizedHermitianMatrix _ = _
    rw [hx, normalizedHermitianMatrix_add]
    rfl
  rw [heq]
  exact mul_le_mul_of_nonneg_left (MinkowskiDeterminant.re_det_le_re_det_add hxS hxT)
    (by positivity)

private theorem fullPositive_add {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    {S T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))}
    (hS : IsFullPositive S) (hT : IsFullPositive T) : IsFullPositive (S + T) := by
  intro e α hα
  exact add_nonneg (hS e α hα) (hT e α hα)

private theorem measure_le_of_finite_restrictions {X : Type*} [MeasurableSpace X]
    {k : ℕ} (U : Fin k → Set X) (hU : ∀ i, MeasurableSet (U i))
    (hcover : ⋃ i, U i = univ) {μ ν : Measure X}
    (hlocal : ∀ i, μ.restrict (U i) ≤ ν.restrict (U i)) : μ ≤ ν := by
  have hμ := FiniteMeasureGluing.glue_eq_of_restrict_eq U (fun _ => μ) hU hcover μ (fun _ => rfl)
  have hν := FiniteMeasureGluing.glue_eq_of_restrict_eq U (fun _ => ν) hU hcover ν (fun _ => rfl)
  have hdi (i : Fin k) : μ.restrict (disjointed U i) ≤ ν.restrict (disjointed U i) := by
    have h := Measure.restrict_mono_measure (hlocal i) (disjointed U i)
    simpa only [Measure.restrict_restrict_of_subset (disjointed_subset U i)] using h
  apply Measure.le_iff.mpr
  intro A hA
  rw [← hμ, ← hν]
  change (Measure.sum (fun i => μ.restrict (disjointed U i))) A ≤
    (Measure.sum (fun i => ν.restrict (disjointed U i))) A
  rw [Measure.sum_apply _ hA, Measure.sum_apply _ hA]
  exact ENNReal.tsum_le_tsum fun i => Measure.le_iff'.mp (hdi i) A

/-- The entire original global AC top measure increases under arbitrary
full-positive addition. Compactness supplies the cover internally. -/
theorem globalACtopMeasure_le_add
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M] [CompactSpace M]
    (S T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hS : IsFullPositive S) (hT : IsFullPositive T) :
    globalACtopMeasure S hS ≤ globalACtopMeasure (S + T) (fullPositive_add hS hT) := by
  classical
  let V : M → Set M := fun x => (complexChartAt (n := m + 1) x).val.source
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V
    (fun x => (complexChartAt (n := m + 1) x).val.open_source)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_complexChartAt_source x⟩)
  let a := (Fintype.equivFin t).symm
  let E : Fin (Fintype.card t) → ComplexChart (m + 1) M := fun i => complexChartAt (a i).val
  let Uc : Fin (Fintype.card t) → Set M := fun i => (E i).val.source
  have hcover : ⋃ i, Uc i = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht (mem_univ x))
    exact mem_iUnion.mpr ⟨a.symm ⟨y, hyt⟩, by simpa [Uc, E] using hxy⟩
  apply measure_le_of_finite_restrictions Uc (fun i => (E i).val.open_source.measurableSet) hcover
  intro i
  rw [globalACtopMeasure_restrict_chart, globalACtopMeasure_restrict_chart]
  let e := E i
  have heq : chartSpanCurrent (S + T) e = chartSpanCurrent S e + chartSpanCurrent T e := by
    ext γ φ
    rfl
  have hl := acTopMeasure_le_add (isPositive_chartSpanCurrent S hS e)
    (isPositive_chartSpanCurrent T hT e)
  have hc : acTopMeasure (isPositive_chartSpanCurrent (S + T) (fullPositive_add hS hT) e) =
      acTopMeasure ((isPositive_chartSpanCurrent S hS e).add (isPositive_chartSpanCurrent T hT e)) := by
    congr 1
  rw [← hc] at hl
  apply Measure.le_iff'.mpr
  intro A
  let j : e.val.target → M := fun z => ((e.val.toHomeomorphSourceTarget).symm z : M)
  have hj : MeasurableEmbedding j :=
    (MeasurableEmbedding.subtype_coe e.val.open_source.measurableSet).comp
      (e.val.toHomeomorphSourceTarget).symm.measurableEmbedding
  have hsub : MeasurableEmbedding (Subtype.val : e.val.target → ComplexModel (m + 1)) :=
    MeasurableEmbedding.subtype_coe e.val.open_target.measurableSet
  change ((acTopMeasure (isPositive_chartSpanCurrent S hS e)).comap
      (Subtype.val : e.val.target → ComplexModel (m + 1))).map j A ≤
    ((acTopMeasure (isPositive_chartSpanCurrent (S + T) (fullPositive_add hS hT) e)).comap
      (Subtype.val : e.val.target → ComplexModel (m + 1))).map j A
  rw [hj.map_apply, hj.map_apply, hsub.comap_apply, hsub.comap_apply]
  exact Measure.le_iff'.mp hl _

end SGPT.Foundations.Analysis.Pending.PositiveCurrentACTopMonotonicity

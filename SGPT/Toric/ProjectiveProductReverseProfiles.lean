import SGPT.Toric.ProjectiveProductNativeCharts
import SGPT.Toric.ProjectiveProductGrowth
import SGPT.Toric.Conjugacy
import SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
open scoped Topology RealInnerProductSpace

/-- The literal nonzero-coordinate inversion used by the original binary chart. -/
def projectiveProductCoordinateInverse {n : ℕ} (ε : Fin n → Bool)
    (z : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 (fun i => if ε i then (z i)⁻¹ else z i)

/-- The genuine linear reflection of original logarithmic coordinates. -/
def projectiveProductChartReflection {n : ℕ} (ε : Fin n → Bool) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 (fun i => if ε i then -(x i) else x i)
  map_add' x y := by
    ext i
    change (if ε i then -(x i + y i) else x i + y i) = _
    cases hε : ε i <;> simp [hε, add_comm]
  map_smul' a x := by
    ext i
    change (if ε i then -(a * x i) else a * x i) = _
    cases hε : ε i <;> simp [hε]

/-- The exact linear correction attached to the inverted original coordinates. -/
def projectiveProductChartLinearTerm {n : ℕ} (ε : Fin n → Bool) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ where
  toFun x := ∑ i : Fin n, if ε i then x i else 0
  map_add' x y := by
    change (∑ i : Fin n, if ε i then x i + y i else 0) = _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases ε i <;> simp
  map_smul' a x := by
    change (∑ i : Fin n, if ε i then a * x i else 0) =
      a * ∑ i : Fin n, if ε i then x i else 0
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases ε i <;> simp

/-- The actual corrected finite convex profile in an arbitrary binary chart. -/
def projectiveProductChartProfile {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (ε : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f (projectiveProductChartReflection ε x) + projectiveProductChartLinearTerm ε x

/-- Existing linear-precomposition and linear-addition convexity applies to the
literal original reflected chart profile. -/
theorem projectiveProductChartProfile_convex {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ConvexOn ℝ univ f) (ε : Fin n → Bool) :
    ConvexOn ℝ univ (projectiveProductChartProfile f ε) := by
  have h : ConvexOn ℝ univ (f ∘ projectiveProductChartReflection ε) := by
    simpa only [preimage_univ] using hf.comp_linearMap (projectiveProductChartReflection ε)
  exact h.add ((projectiveProductChartLinearTerm ε).convexOn convex_univ)

private theorem coordinateInverse_split_fst (n : ℕ) (ε : Fin (n + 1) → Bool)
    (z : ComplexModel (n + 1)) :
    ((prodModelEquiv n 1).symm (projectiveProductCoordinateInverse ε z)).1 =
      projectiveProductCoordinateInverse (Fin.init ε) ((prodModelEquiv n 1).symm z).1 := by
  ext i
  rfl

private theorem coordinateInverse_split_snd (n : ℕ) (ε : Fin (n + 1) → Bool)
    (z : ComplexModel (n + 1)) :
    ((prodModelEquiv n 1).symm (projectiveProductCoordinateInverse ε z)).2 =
      if ε (Fin.last n) then projectiveModelInverse ((prodModelEquiv n 1).symm z).2
        else ((prodModelEquiv n 1).symm z).2 := by
  ext i
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  change (if ε (Fin.last n) then (z (Fin.last n))⁻¹ else z (Fin.last n)) =
    (if ε (Fin.last n) then projectiveModelInverse ((prodModelEquiv n 1).symm z).2
      else ((prodModelEquiv n 1).symm z).2) 0
  cases ε (Fin.last n) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, projectiveModelInverse,
      projectiveModelEquiv_apply_zero, projectiveModelEquiv_symm_apply] <;> rfl

private theorem projectiveNativeChart_symm_inverse (b : Bool) {z : ComplexModel 1}
    (hz : z 0 ≠ 0) :
    (projectiveNativeChart b).val.symm z =
      (projectiveNativeChart false).val.symm (if b then projectiveModelInverse z else z) := by
  cases b
  · rfl
  · simp only [projectiveNativeChart_val, projectiveModelChart_symm_onePoint,
      Bool.false_eq_true, ↓reduceIte]
    rw [projectiveReciprocal_coe hz]
    congr 1
    simp [projectiveModelInverse, projectiveModelEquiv_apply_zero,
      projectiveModelEquiv_symm_apply]

/-- All original binary inverse quotient sections agree with the literal
preferred inverse section after exactly the prescribed nonzero inversions. -/
theorem projectiveProductNativeChart_symm_inverse : (n : ℕ) → (ε : Fin n → Bool) →
    {z : ComplexModel n} → z ∈ complexTorus n →
    (projectiveProductNativeChart n ε).val.symm z =
      (projectiveProductNativeChart n (fun _ => false)).val.symm
        (projectiveProductCoordinateInverse ε z)
  | 0, _, z, _ => by
    change z = projectiveProductCoordinateInverse _ z
    ext i
    exact Fin.elim0 i
  | n + 1, ε, z, hz => by
    change ((projectiveProductNativeChart n (Fin.init ε)).val.symm
        ((prodModelEquiv n 1).symm z).1,
      (projectiveNativeChart (ε (Fin.last n))).val.symm ((prodModelEquiv n 1).symm z).2) =
      ((projectiveProductNativeChart n (fun _ => false)).val.symm
        ((prodModelEquiv n 1).symm (projectiveProductCoordinateInverse ε z)).1,
      (projectiveNativeChart false).val.symm
        ((prodModelEquiv n 1).symm (projectiveProductCoordinateInverse ε z)).2)
    rw [coordinateInverse_split_fst, coordinateInverse_split_snd]
    apply Prod.ext
    · exact projectiveProductNativeChart_symm_inverse n (Fin.init ε)
        (fun i => hz i.castSucc)
    · exact projectiveNativeChart_symm_inverse _ (hz (Fin.last n))

/-- True original logarithmic coordinates turn the actual binary inversions
into the produced real linear reflection. -/
theorem tropicalization_projectiveProductCoordinateInverse {n : ℕ} (ε : Fin n → Bool)
    (z : ComplexModel n) :
    tropicalization (projectiveProductCoordinateInverse ε z) =
      projectiveProductChartReflection ε (tropicalization z) := by
  ext i
  change 2 * Real.log ‖(if ε i then (z i)⁻¹ else z i)‖ =
    if ε i then -(2 * Real.log ‖z i‖) else 2 * Real.log ‖z i‖
  cases ε i <;> simp [norm_inv, Real.log_inv]

/-- The original scalar FS reciprocal identity adds over the actual coordinates. -/
theorem projectiveProductFSPotential_coordinateInverse {n : ℕ} (ε : Fin n → Bool)
    {z : ComplexModel n} (hz : z ∈ complexTorus n) :
    projectiveProductFSPotential n (projectiveProductCoordinateInverse ε z) =
      projectiveProductFSPotential n z -
        projectiveProductChartLinearTerm ε (tropicalization z) := by
  change (∑ i : Fin n, Real.log (1 + Complex.normSq (if ε i then (z i)⁻¹ else z i))) =
    (∑ i : Fin n, Real.log (1 + Complex.normSq (z i))) -
      ∑ i : Fin n, if ε i then tropicalization z i else 0
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hε : ε i
  · simp
  · simp only [if_true]
    rw [tropicalization_apply_eq_log_norm_sq, ← Complex.normSq_eq_norm_sq]
    exact projectiveFS_scalar_inverse (hz i)

/-- The literal source reverse potential; arbitrary off-chart values are never
used before the actual torus condition, and are masked by the canonical fill. -/
def projectiveProductToricOffPotential {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : projectiveProductSpace n) : EReal :=
  let z := (projectiveProductNativeChart n (fun _ => false)).val p
  ((f (tropicalization z) - projectiveProductFSPotential n z : ℝ) : EReal)

/-- The genuine allchart corrected formula for the original reverse potential,
proved before any extension or target native-PSH assertion. -/
theorem projectiveProductToricOffPotential_corrected_chart {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε : Fin n → Bool)
    {z : ComplexModel n} (hz : z ∈ complexTorus n) :
    projectiveProductToricOffPotential f ((projectiveProductNativeChart n ε).val.symm z) +
      (projectiveProductFSPotential n z : EReal) =
        (projectiveProductChartProfile f ε (tropicalization z) : EReal) := by
  have ht : projectiveProductCoordinateInverse ε z ∈
      (projectiveProductNativeChart n (fun _ => false)).val.target := by
    rw [projectiveProductNativeChart_target]
    exact mem_univ _
  simp only [projectiveProductToricOffPotential,
    projectiveProductNativeChart_symm_inverse n ε hz,
    (projectiveProductNativeChart n (fun _ => false)).val.right_inv ht,
    tropicalization_projectiveProductCoordinateInverse,
    projectiveProductFSPotential_coordinateInverse ε hz, ← EReal.coe_add]
  congr 1
  unfold projectiveProductChartProfile
  ring

/-- The original finite convex function produces the native off-boundary
criterion in EVERY actual native atlas chart. -/
theorem thetaPshOff_projectiveProductToricOffPotential {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ConvexOn ℝ univ f) :
    ThetaPshOff (projectiveProductFSBackground n).form.val (projectiveProductTorus n)ᶜ
      (projectiveProductToricOffPotential f) := by
  intro e z _ hz
  obtain ⟨ε, rfl⟩ := projectiveProductNativeChart_exhaustive e
  have hzT : z ∈ complexTorus n :=
    (projectiveProductTorus_chart_symm n ε z).mp (by simpa only [mem_compl_iff, not_not] using hz)
  refine ⟨complexTorus n, projectiveProductFSPotential n, hzT,
    (projectiveProductFSPotential_localPotential n ε).mono (isOpen_complexTorus n)
      (subset_univ _), ?_⟩
  have hp := plurisubharmonicOn_tropicalPullback_of_convexOn
    (projectiveProductChartProfile_convex hf ε)
  intro y hy
  apply (hp y hy).congr
  filter_upwards [(isOpen_complexTorus n).mem_nhds hy] with w hw
  exact (projectiveProductToricOffPotential_corrected_chart f ε hw).symm

/-- Actual original cube support growth manufactures a finite upper bound for
the native reverse branch on the original dense torus. -/
theorem exists_upper_bound_projectiveProductToricOffPotential {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (euclideanUnitCube n)) :
    ∃ C : ℝ, ∀ p ∈ projectiveProductTorus n,
      projectiveProductToricOffPotential f p ≤ (C : EReal) := by
  obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real _ _).mp hf.2
  refine ⟨C, fun p hp => ?_⟩
  have hz := hp
  rw [← projectiveProductTorus_chart_source n] at hz
  let z := (projectiveProductNativeChart n (fun _ => false)).val p
  have hzT : z ∈ complexTorus n := hz.2
  have h := hC (tropicalization z)
  rw [support_euclideanUnitCube, ← EReal.coe_add] at h
  have hreal := EReal.coe_le_coe_iff.mp h
  have hρ : (∑ i : Fin n, max 0 (tropicalization z i)) ≤ projectiveProductFSPotential n z := by
    rw [← projectiveProductReferenceProfile_tropicalization hzT]
    exact Finset.sum_le_sum (fun i _ => max_le_projectiveLineLogPartition _)
  apply EReal.coe_le_coe_iff.mpr
  change f (tropicalization z) - projectiveProductFSPotential n z ≤ C
  linarith

end SGPT.Toric
